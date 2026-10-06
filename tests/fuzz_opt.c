/* Differential test: the optimizer must not change what a program does.
 *
 *   cc -std=c11 -DMY_OPT_NO_MAIN -Itests/ccc_model tests/fuzz_opt.c -o fuzz_opt && ./fuzz_opt 2000
 *
 * Random programs on the IR model mix constant, copy and arithmetic
 * assignments, calls f(x) that print their argument and modify a variable
 * (as a function with access to it through a pointer would), stores through a
 * pointer, forward branches and counted loops built from backward branches.
 * Each program is built twice from the same seed; one copy is optimized. An
 * interpreter runs both, and the sequences of call arguments (the observable
 * behaviour) must be identical. */
#define MY_OPT_NO_MAIN
#include "../my_opt.c"

sub_struct *subroutines[MAX_SUBROUTINES];
int subroutine_number;
int i_node_number;
void dump_ast(void) {}

#define NV 10  /* variables 0..7 general, 8 loop counter, 9 pointer target */
static identifier_struct VARS[16];
static unsigned long long rng;
static unsigned rnd(unsigned n) { rng = rng * 6364136223846793005ull + 1442695040888963407ull; return (unsigned)(rng >> 33) % n; }

static expr_node *mk(oper_t op, expr_node *l, expr_node *r) {
    expr_node *e = calloc(1, sizeof *e);
    e->operator = op; e->left = l; e->right = r;
    return e;
}
static expr_node *V(int i) { expr_node *e = mk(IDENTIFIER, NULL, NULL); VARS[i].rec_index = i; e->identifier = &VARS[i]; return e; }
static expr_node *C(long long v) {
    expr_node *e = mk(CONSTANT, NULL, NULL);
    e->constant = calloc(1, sizeof *e->constant);
    e->constant->const_type = TYPE_INT; e->constant->ivalue = v;
    return e;
}
static instr_node *ins(instr_type_t t, expr_node *e) { instr_node *i = calloc(1, sizeof *i); i->type = t; i->expression = e; return i; }

static instr_node *list[512];
static int n;
static void emit(instr_node *i) { list[n++] = i; }

static expr_node *operand(void) { return rnd(3) ? V((int)rnd(8)) : C((long long)rnd(7) - 2); }

static void random_statement(void) {
    int x = (int)rnd(8);
    switch (rnd(9)) {
    case 0: emit(ins(EXPRESSION, mk(ASSIGN, V(x), C((long long)rnd(9) - 3)))); break;
    case 1: emit(ins(EXPRESSION, mk(ASSIGN, V(x), V((int)rnd(8))))); break;
    case 2: case 3: {
        static const oper_t ops[4] = {PLUSOP, MINUSOP, MULOP, LSHIFT};
        oper_t op = ops[rnd(4)];
        expr_node *r = op == LSHIFT ? C(rnd(3)) : operand();
        emit(ins(EXPRESSION, mk(ASSIGN, V(x), mk(op, operand(), r))));
        break;
    }
    case 4: {  /* nested pure expression: x = (a op b) op c */
        emit(ins(EXPRESSION, mk(ASSIGN, V(x), mk(PLUSOP, mk(MULOP, operand(), operand()), operand()))));
        break;
    }
    case 5: {  /* f(x) */
        expr_node *c = mk(FUNCALL, V(15), NULL);
        c->expression_list = calloc(1, sizeof *c->expression_list);
        c->expression_list->expression = V(x);
        emit(ins(EXPRESSION, c));
        break;
    }
    case 6:  /* *p = value  (p points to variable 9) */
        emit(ins(EXPRESSION, mk(ASSIGN, mk(DEREF, V(9), NULL), operand())));
        break;
    case 7:  /* x = *p */
        emit(ins(EXPRESSION, mk(ASSIGN, V(x), mk(DEREF, V(9), NULL))));
        break;
    default:  /* x += operand */
        emit(ins(EXPRESSION, mk(ASSIGNADD, V(x), operand())));
        break;
    }
}

/* Builds the program; forward branches and loops are patched after layout. */
static sub_struct *build(unsigned long long seed) {
    rng = seed;
    n = 0;
    int stmts = 8 + (int)rnd(40);
    for (int s = 0; s < stmts && n < 480; s++) {
        unsigned k = rnd(10);
        if (k == 0) {                             /* forward branch, targets patched below */
            emit(ins(IF_BRANCH, mk(LTOP, operand(), operand())));
        } else if (k == 1) {                      /* counted loop: c = k; L: body; c -= 1; if (0 < c) goto L */
            emit(ins(EXPRESSION, mk(ASSIGN, V(8), C(1 + rnd(4)))));
            int head = n;
            int body = 1 + (int)rnd(4);
            for (int b = 0; b < body; b++) {
                random_statement();
                expr_node *l = list[n - 1]->expression->left;
                if (l && l->operator == IDENTIFIER && l->identifier->rec_index == 8) list[n - 1]->expression->left = V(0);
            }
            emit(ins(EXPRESSION, mk(ASSIGNSUB, V(8), C(1))));
            instr_node *br = ins(IF_BRANCH, mk(LTOP, C(0), V(8)));
            br->instruction = list[head];
            emit(br);
        } else {
            random_statement();
        }
    }
    for (int x = 0; x < 8; x++) {  /* make every variable observable at the end */
        expr_node *c = mk(FUNCALL, V(15), NULL);
        c->expression_list = calloc(1, sizeof *c->expression_list);
        c->expression_list->expression = V(x);
        emit(ins(EXPRESSION, c));
    }
    for (int k = 0; k + 1 < n; k++) list[k]->next = list[k + 1];
    for (int k = 0; k < n; k++)  /* forward branches: true -> next, false -> up to 4 instructions ahead */
        if (list[k]->type == IF_BRANCH && !list[k]->instruction) {
            int span = n - k - 1 > 4 ? 4 : n - k - 1;
            list[k]->instruction = list[k + 1];
            list[k]->tail_instruction = list[k + 1 + rnd((unsigned)span)];
        }
    sub_struct *s = calloc(1, sizeof *s);
    s->sub_first = list[0];
    s->items = 16;
    return s;
}

/* ---------------- interpreter ---------------- */
static long long trace[4096];
static int ntrace;

static long long eval(const expr_node *e, long long *v);

static long long *lvalue(const expr_node *e, long long *v) {
    if (e->operator == IDENTIFIER) return &v[e->identifier->rec_index];
    if (e->operator == DEREF) return &v[9];
    return NULL;
}

static long long eval(const expr_node *e, long long *v) {
    switch (e->operator) {
    case IDENTIFIER: return v[e->identifier->rec_index];
    case CONSTANT: return e->constant->ivalue;
    case PLUSOP: return eval(e->left, v) + eval(e->right, v);
    case MINUSOP: return eval(e->left, v) - eval(e->right, v);
    case MULOP: return eval(e->left, v) * eval(e->right, v);
    case LSHIFT: return (long long)((unsigned long long)eval(e->left, v) << (eval(e->right, v) & 31));
    case LTOP: return eval(e->left, v) < eval(e->right, v);
    case DEREF: return v[9];
    case FUNCALL: {
        long long a = e->expression_list ? eval(e->expression_list->expression, v) : 0;
        if (ntrace < 4096) trace[ntrace++] = a;
        v[9] = v[9] * 31 + a + 1;  /* the callee writes through its pointer */
        return 0;
    }
    case ASSIGN: { long long r = eval(e->right, v); *lvalue(e->left, v) = r; return r; }
    case ASSIGNADD: { long long r = eval(e->right, v); *lvalue(e->left, v) += r; return 0; }
    case ASSIGNSUB: { long long r = eval(e->right, v); *lvalue(e->left, v) -= r; return 0; }
    default: fprintf(stderr, "unexpected operator %d\n", e->operator); exit(2);
    }
}

static int interpret(sub_struct *s) {
    long long v[16] = {0};
    for (int i = 0; i < 16; i++) v[i] = 3 * i + 1;
    ntrace = 0;
    instr_node *pc = s->sub_first;
    for (int steps = 0; pc && steps < 100000; steps++) {
        if (pc->type == IF_BRANCH) {
            pc = eval(pc->expression, v) ? pc->instruction : (pc->tail_instruction ? pc->tail_instruction : pc->next);
        } else if (pc->type == S_GOTO) {
            pc = pc->target;
        } else {
            eval(pc->expression, v);
            pc = pc->next;
        }
    }
    return pc == NULL;
}

int main(int argc, char **argv) {
    int count = argc > 1 ? atoi(argv[1]) : 2000;
    int bad = 0, changed = 0;
    long long ref[4096];
    int nref;
    for (int t = 0; t < count; t++) {
        unsigned long long seed = 0x9e3779b97f4a7c15ull * (unsigned long long)(t + 1);
        sub_struct *a = build(seed);
        if (!interpret(a)) continue;  /* did not terminate (cannot happen with counted loops) */
        nref = ntrace;
        memcpy(ref, trace, sizeof(long long) * (size_t)ntrace);
        sub_struct *b = build(seed);
        subroutines[0] = b;
        subroutine_number = 1;
        my_opt_verbose = 0;
        my_optimization();
        changed += g_stats.constants_propagated + g_stats.copies_propagated + g_stats.cse + g_stats.dead_removed +
                   g_stats.simplified + g_stats.jumps_removed > 0;
        interpret(b);
        if (ntrace != nref || memcmp(ref, trace, sizeof(long long) * (size_t)ntrace) != 0) {
            bad++;
            if (bad <= 5) printf("MISMATCH seed %d: %d calls before, %d after\n", t + 1, nref, ntrace);
        }
    }
    printf("%d random programs, %d changed by the optimizer, %d behaved differently after optimization\n", count, changed, bad);
    return bad ? 1 : 0;
}

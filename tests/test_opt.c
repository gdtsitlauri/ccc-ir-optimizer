/* Unit tests for my_opt.c on hand-built IR (tests/ccc_model).
 *
 *   cc -std=c11 -DMY_OPT_NO_MAIN -Itests/ccc_model tests/test_opt.c -o test_opt && ./test_opt
 *
 * Each test builds a small subroutine, runs the optimizer and checks the
 * result. The negative tests check that the IR is left unchanged when a
 * transformation would be unsafe, including the cases that the first version
 * of the optimizer got wrong. */
#define MY_OPT_NO_MAIN
#include "../my_opt.c"

sub_struct *subroutines[MAX_SUBROUTINES];
int subroutine_number;
int i_node_number;
void dump_ast(void) {}

/* ---------------- IR builders ---------------- */
static identifier_struct VARS[16];
static int node_counter;

static expr_node *mk(oper_t op, expr_node *l, expr_node *r) {
    expr_node *e = calloc(1, sizeof *e);
    e->operator = op; e->left = l; e->right = r;
    return e;
}
static expr_node *V(int idx) {  /* variable reference */
    expr_node *e = mk(IDENTIFIER, NULL, NULL);
    VARS[idx].rec_index = idx;
    e->identifier = &VARS[idx];
    return e;
}
static expr_node *C(long long v) {
    expr_node *e = mk(CONSTANT, NULL, NULL);
    const_struct *c = calloc(1, sizeof *c);
    c->const_type = TYPE_INT; c->ivalue = v;
    e->constant = c;
    return e;
}
static expr_node *CALL(void) { return mk(FUNCALL, V(15), NULL); }
static expr_node *ASG(int x, expr_node *rhs) { return mk(ASSIGN, V(x), rhs); }

static instr_node *ins(instr_type_t t, expr_node *e) {
    instr_node *i = calloc(1, sizeof *i);
    i->type = t; i->expression = e; i->node_i = node_counter++;
    return i;
}
static instr_node *S(expr_node *e) { return ins(EXPRESSION, e); }

static sub_struct *program(int n, instr_node **v) {
    for (int k = 0; k + 1 < n; k++) v[k]->next = v[k + 1];
    sub_struct *s = calloc(1, sizeof *s);
    s->sub_first = n ? v[0] : NULL;
    s->items = 16;
    subroutines[0] = s;
    subroutine_number = 1;
    return s;
}

static void run(void) {
    my_opt_verbose = 0;
    my_optimization();
}

/* ---------------- checks ---------------- */
static int failures, checks;
#define CHECK(cond, msg) do { checks++; if (!(cond)) { failures++; printf("  FAIL: %s (line %d)\n", msg, __LINE__); } } while (0)

static int is_var(const expr_node *e, int idx) { return e && e->operator == IDENTIFIER && e->identifier->rec_index == idx; }
static int is_const(const expr_node *e, long long v) { return e && e->operator == CONSTANT && e->constant->ivalue == v; }
static int in_list(const sub_struct *s, const instr_node *x) {
    for (instr_node *i = s->sub_first; i; i = i->next) if (i == x) return 1;
    return 0;
}

/* Variables: 0..9 locals; 15 is a function name. Every test keeps the
 * interesting results alive by using them in a call: f(r). */
static instr_node *USE(int x) { expr_node *c = CALL(); expr_list *a = calloc(1, sizeof *a); a->expression = V(x); c->expression_list = a; return S(c); }

static void test_constant_propagation(void) {
    printf("constant propagation\n");
    /* a = 5; b = a + 1; f(b) */
    instr_node *v[] = {S(ASG(0, C(5))), S(ASG(1, mk(PLUSOP, V(0), C(1)))), USE(1)};
    program(3, v);
    run();
    CHECK(is_const(v[1]->expression->right->left, 5), "a replaced by 5 in b = a + 1");
}

static void test_cp_not_across_call(void) {
    printf("constant propagation stops at a call\n");
    /* a = 5; g(); b = a + 1; f(b)   (g may change a through a pointer) */
    instr_node *v[] = {S(ASG(0, C(5))), S(CALL()), S(ASG(1, mk(PLUSOP, V(0), C(1)))), USE(1)};
    program(4, v);
    run();
    CHECK(is_var(v[2]->expression->right->left, 0), "a kept after a call");
}

static void test_cp_not_into_loop(void) {
    printf("constant propagation does not enter a loop body\n");
    /* i = 0; while (c) { t = i + 1; i = t; } f(i)
       Built with the body in a separate list (instruction pointer). */
    instr_node *body0 = S(ASG(2, mk(PLUSOP, V(0), C(1))));
    instr_node *body1 = S(ASG(0, V(2)));
    body0->next = body1;
    instr_node *loop = ins(WHILE_LOOP, mk(LTOP, V(0), C(10)));
    loop->instruction = body0;
    body0->parent = loop; body1->parent = loop;
    instr_node *v[] = {S(ASG(0, C(0))), loop, USE(0)};
    program(3, v);
    run();
    CHECK(is_var(body0->expression->right->left, 0), "i not replaced inside the body");
    CHECK(is_var(v[2]->expression->expression_list->expression, 0), "i not replaced after the loop");
}

static void test_cp_not_at_jump_target(void) {
    printf("constant propagation does not cross a jump target\n");
    /* a = 1; L: b = a + 1; f(b); goto L   (flat layout) */
    instr_node *lab = S(ASG(1, mk(PLUSOP, V(0), C(1))));
    instr_node *g = ins(S_GOTO, NULL);
    g->target = lab;
    instr_node *v[] = {S(ASG(0, C(1))), lab, USE(1), g};
    program(4, v);
    run();
    CHECK(is_var(lab->expression->right->left, 0), "a kept at a jump target");
}

static void test_copy_propagation(void) {
    printf("copy propagation\n");
    /* a = b; c = a + 1; b = 7; d = a + 2; f(c); f(d) */
    instr_node *v[] = {S(ASG(0, V(1))), S(ASG(2, mk(PLUSOP, V(0), C(1)))), S(ASG(1, C(7))),
                       S(ASG(3, mk(PLUSOP, V(0), C(2)))), USE(2), USE(3)};
    program(6, v);
    run();
    CHECK(is_var(v[1]->expression->right->left, 1), "a replaced by b before b changes");
    CHECK(is_var(v[3]->expression->right->left, 0), "a kept after b is redefined");
    CHECK(is_var(v[0]->expression->left, 0), "left-hand side of a = b untouched (first version rewrote it)");
    CHECK(VARS[0].rec_index == 0 && VARS[1].rec_index == 1, "symbol records not modified (first version changed rec_index)");
}

static void test_cse(void) {
    printf("common-subexpression elimination\n");
    /* x = a * b; y = a * b; f(x); f(y) */
    instr_node *v[] = {S(ASG(2, mk(MULOP, V(0), V(1)))), S(ASG(3, mk(MULOP, V(0), V(1)))), USE(2), USE(3)};
    program(4, v);
    run();
    CHECK(is_var(v[1]->expression->right, 2), "y = a * b becomes y = x");
}

static void test_cse_killed(void) {
    printf("common-subexpression elimination respects redefinitions\n");
    /* x = a * b; a = 3; y = a * b; f(x); f(y) */
    instr_node *v[] = {S(ASG(2, mk(MULOP, V(0), V(1)))), S(ASG(0, C(3))), S(ASG(3, mk(MULOP, V(0), V(1)))), USE(2), USE(3)};
    program(5, v);
    run();
    CHECK(v[2]->expression->right->operator == MULOP, "y = a * b kept after a changes");
}

static void test_dce(void) {
    printf("dead-code elimination\n");
    /* t = a + 1; u = g(); f(a)   -> t is never read and has no side effect */
    instr_node *v[] = {S(ASG(4, mk(PLUSOP, V(0), C(1)))), S(ASG(5, CALL())), USE(0)};
    sub_struct *s = program(3, v);
    run();
    CHECK(!in_list(s, v[0]), "t = a + 1 removed");
    CHECK(in_list(s, v[1]), "u = g() kept: the call has side effects");
}

static void test_dce_chain(void) {
    printf("dead-code elimination repeats until nothing changes\n");
    /* p = a; q = p + 1; f(a)  -> q dead, then p dead */
    instr_node *v[] = {S(ASG(4, V(0))), S(ASG(5, mk(PLUSOP, V(4), C(1)))), USE(0)};
    sub_struct *s = program(3, v);
    run();
    CHECK(!in_list(s, v[0]) && !in_list(s, v[1]), "both dead assignments removed");
}

static void test_dce_keeps_targets(void) {
    printf("dead-code elimination keeps jump targets\n");
    /* L: t = 1; f(a); goto L   -- t is never read, but L is a jump target */
    instr_node *dead = S(ASG(4, C(1)));
    instr_node *g = ins(S_GOTO, NULL);
    g->target = dead;
    instr_node *v[] = {dead, USE(0), g};
    sub_struct *s = program(3, v);
    run();
    CHECK(in_list(s, dead), "a jump target is never removed");
}

static void test_jump_cleanup(void) {
    printf("jump cleanup\n");
    /* a = x + y; goto L; L: b = x + 2; f(a); f(b) -- and consecutive statements stay */
    instr_node *l = S(ASG(1, mk(PLUSOP, V(6), C(2))));
    instr_node *g = ins(S_GOTO, NULL);
    g->target = l;
    instr_node *v[] = {S(ASG(0, mk(PLUSOP, V(6), V(7)))), g, l, USE(0), USE(1)};
    sub_struct *s = program(5, v);
    run();
    CHECK(!in_list(s, g), "goto to the next instruction removed");
    CHECK(in_list(s, v[0]) && in_list(s, l), "consecutive statements kept (first version deleted every second one)");
}

static void test_simplification(void) {
    printf("algebraic simplification\n");
    /* x = a + 0; y = 1 * b; f(x); f(y) */
    instr_node *v[] = {S(ASG(2, mk(PLUSOP, V(0), C(0)))), S(ASG(3, mk(MULOP, C(1), V(1)))), USE(2), USE(3)};
    program(4, v);
    run();
    CHECK(is_var(v[0]->expression->right, 0), "a + 0 -> a");
    CHECK(is_var(v[1]->expression->right, 1), "1 * b -> b");
}

static void test_no_rewrite_under_unknown_operator(void) {
    printf("no rewriting under other operators (address-of)\n");
    /* a = 5; p = &a; f(p) -- &a must stay &a */
    instr_node *v[] = {S(ASG(0, C(5))), S(ASG(1, mk(ADDROF, V(0), NULL))), USE(1)};
    program(3, v);
    run();
    CHECK(is_var(v[1]->expression->right->left, 0), "&a not turned into &5");
}

static void test_pointer_store_clobbers(void) {
    printf("a store through a pointer discards facts\n");
    /* a = 5; *p = 9; b = a + 1; f(b) */
    instr_node *v[] = {S(ASG(0, C(5))), S(mk(ASSIGN, mk(DEREF, V(1), NULL), C(9))), S(ASG(2, mk(PLUSOP, V(0), C(1)))), USE(2)};
    program(4, v);
    run();
    CHECK(is_var(v[2]->expression->right->left, 0), "a kept after *p = 9");
}

static void test_loop_analysis(void) {
    printf("natural-loop analysis\n");
    /* L: a = a + 1; if (a < 10) goto L; f(a)   (flat layout with a back edge) */
    instr_node *l = S(ASG(0, mk(PLUSOP, V(0), C(1))));
    instr_node *br = ins(IF_BRANCH, mk(LTOP, V(0), C(10)));
    instr_node *after = USE(0);
    br->instruction = l;
    br->tail_instruction = after;
    instr_node *v[] = {S(ASG(0, C(0))), l, br, after};
    program(4, v);
    run();
    CHECK(g_stats.loops == 1, "one natural loop found");
    CHECK(g_stats.blocks == 3, "three basic blocks");
}

int main(void) {
    test_constant_propagation();
    test_cp_not_across_call();
    test_cp_not_into_loop();
    test_cp_not_at_jump_target();
    test_copy_propagation();
    test_cse();
    test_cse_killed();
    test_dce();
    test_dce_chain();
    test_dce_keeps_targets();
    test_jump_cleanup();
    test_simplification();
    test_no_rewrite_under_unknown_operator();
    test_pointer_store_clobbers();
    test_loop_analysis();
    printf("\n%d/%d checks passed\n", checks - failures, checks);
    return failures ? 1 : 0;
}

/* ir_interp.c - executes a CCC IR file, for differential testing of the optimizer.
 *
 *   ir_interp file.ir [runs] [first_seed] [all]
 *
 * Runs the root function of the program (mainfuncindex), or with `all` every
 * subroutine, `runs` times, each time with inputs drawn from a seeded generator,
 * and prints one line per run:
 *
 *   <function> seed <s> ok ret <value> state <hash> steps <n>
 *   <function> seed <s> timeout | error:<reason>
 *
 * The hash covers the return value and every memory cell the caller can observe
 * (the cells behind pointer, array and struct arguments, and the globals).
 * `steps` counts executed instructions and evaluated expression nodes. Running
 * the original and the optimized IR with the same seeds must print the same lines
 * apart from `steps`. (The IR loader prints its own progress lines first.)
 *
 * Semantics: C integer arithmetic on the declared types (char 8, short 16, int
 * and long 32, long long 64 bits, signed or unsigned), arrays, structs and
 * pointers over a flat memory of 64-bit cells (one cell per scalar), calls by
 * value, switch with fall-through, break and continue by target. Floating
 * point, unions and goto are reported as errors.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "csensetypes.h"
#include "intermediate.h"
#include "irloadstore.h"

extern int subroutine_number;
extern sub_struct *subroutines[];
extern int cur_glob_index;
extern static_record globals[];
extern int mainfuncindex;

typedef long long i64;
typedef unsigned long long u64;

/* ---------------------------------------------------------------- errors */
static char err_reason[128];
static int err_set;
static void fail(const char *why, int node) {
    if (!err_set) snprintf(err_reason, sizeof err_reason, "%s@%d", why, node);
    err_set = 1;
}

static long long steps, step_limit = 2000000;
static int timed_out;

/* ---------------------------------------------------------------- memory */
#define MEM_CELLS (1 << 22)
static i64 *mem;
static int mem_top; /* cells [1, mem_top) are allocated; address 0 is null */

static int alloc_cells(int n) {
    if (n <= 0) n = 1;
    if (mem_top + n > MEM_CELLS) { fail("out of memory", 0); return 0; }
    int a = mem_top;
    memset(mem + a, 0, sizeof(i64) * (size_t)n);
    mem_top += n;
    return a;
}

static int valid(i64 a) { return a > 0 && a < mem_top; }

static i64 load(i64 a, int node) {
    if (!valid(a)) { fail("bad load", node); return 0; }
    return mem[a];
}
static void store(i64 a, i64 v, int node) {
    if (!valid(a)) { fail("bad store", node); return; }
    mem[a] = v;
}

/* ---------------------------------------------------------------- types */
static int cells(type_t t, const type_struct *s) {
    if (t & TYPE_ARRAY) {
        if (!s) return 1;
        int n = s->s_pointer.items;
        int e = cells(s->s_pointer.type, s->s_pointer.structure);
        return (n > 0 ? n : 1) * e;
    }
    if (t & TYPE_UNION) { fail("union", 0); return 1; }
    if (t & TYPE_STRUCT) {
        if (!s) { fail("struct type", 0); return 1; }
        int n = 0;
        for (const struct_field *fl = s->s_struct.fields; fl; fl = fl->next) n += cells(fl->type, fl->structure);
        return n > 0 ? n : 1;
    }
    return 1;
}

/* struct fields: cell offset of field number k, and its type */
static const struct_field *field_at(const type_struct *s, int k, int *offset) {
    *offset = 0;
    if (!s) return NULL;
    int pos = 0;
    for (const struct_field *fl = s->s_struct.fields; fl; fl = fl->next, pos++) {
        if (pos == k) return fl;
        *offset += cells(fl->type, fl->structure);
    }
    return NULL;
}

/* values of these types are handled by address: arrays and structs */
static int by_address(type_t t) { return (t & (TYPE_ARRAY | TYPE_STRUCT)) != 0; }

/* cells of the element a pointer or array of type (t, s) points to */
static int elem_cells(type_t t, const type_struct *s) {
    if (!(t & (TYPE_POINTER | TYPE_ARRAY)) || !s) return 1;
    return cells(s->s_pointer.type, s->s_pointer.structure);
}

static i64 conv(i64 v, type_t t) {
    if (t & (TYPE_POINTER | TYPE_ARRAY)) return v;
    if (t & (TYPE_FLOAT | TYPE_DOUBLE)) { fail("float", 0); return v; }
    int u = (t & TYPE_UNSIGNED) != 0;
    if (t & TYPE_CHAR) return u ? (i64)(unsigned char)v : (i64)(signed char)v;
    if (t & TYPE_SHORT) return u ? (i64)(unsigned short)v : (i64)(short)v;
    if (t & TYPE_LONGLONG) return v;
    if (t & (TYPE_INT | TYPE_LONG | TYPE_ENUM)) return u ? (i64)(unsigned int)v : (i64)(int)v;
    return v;
}

static int is_unsigned(type_t t) { return (t & TYPE_UNSIGNED) || (t & TYPE_POINTER); }
static int is_ptr(type_t t) { return (t & (TYPE_POINTER | TYPE_ARRAY)) != 0; }

/* ---------------------------------------------------------------- frames */
typedef struct { sub_struct *sub; int base[0x10000]; } Frame;
static int global_base[100000];

static i64 var_addr(const id_struct *id, Frame *f, int node) {
    if (id->rec_index < 0) {
        int k = -id->rec_index;
        if (!f || k >= f->sub->items || k >= 0x10000) { fail("bad local", node); return 0; }
        return f->base[k];
    }
    if (id->rec_index >= cur_glob_index) { fail("bad global", node); return 0; }
    return global_base[id->rec_index];
}

/* ---------------------------------------------------------------- expressions */
static i64 rv(expr_node *e, Frame *f);
static i64 lv(expr_node *e, Frame *f);
static i64 call(sub_struct *sub, expr_list *args, Frame *caller, int node);

static i64 lv(expr_node *e, Frame *f) {
    if (!e || err_set) return 0;
    switch (e->operator) {
    case IDENTIFIER:
        return var_addr(e->identifier, f, e->node_i);
    case ARRAY: {
        i64 base = rv(e->left, f); /* array decays to its address */
        i64 idx = rv(e->right, f);
        return base + idx * cells(e->type, e->structure);
    }
    case POINTSTO:
        return rv(e->left, f);
    case FIELD: case PFIELD: {
        const type_struct *st = e->operator == FIELD ? e->left->structure
                                : (e->left->structure ? e->left->structure->s_pointer.structure : NULL);
        i64 base = e->operator == FIELD ? lv(e->left, f) : rv(e->left, f);
        int off;
        if (!e->right || e->right->operator != CONSTANT || !field_at(st, (int)e->right->constant->ivalue, &off)) {
            fail("field", e->node_i);
            return 0;
        }
        return base + off;
    }
    case FUNCALL: case ASSIGN:
        fail("struct value", e->node_i);
        return 0;
    default:
        fail("not an lvalue", e->node_i);
        return 0;
    }
}

static i64 arith(oper_t op, i64 a, i64 b, type_t t, type_t ta, int node) {
    int u = is_unsigned(t);
    switch (op) {
    case PLUSOP: case ASSIGNADD: return a + b;
    case MINUSOP: case ASSIGNSUB: return a - b;
    case MULOP: case ASSIGNMUL: return u ? (i64)((u64)a * (u64)b) : a * b;
    case DIVOP: case ASSIGNDIV:
        if (b == 0) { fail("division by zero", node); return 0; }
        return u ? (i64)((u64)a / (u64)b) : a / b;
    case MODOP: case ASSIGNMOD:
        if (b == 0) { fail("division by zero", node); return 0; }
        return u ? (i64)((u64)a % (u64)b) : a % b;
    case LSHIFT: case ASSIGNLSH: return (i64)((u64)a << (b & 63));
    case RSHIFT: case ASSIGNRSH: return is_unsigned(ta) ? (i64)((u64)a >> (b & 63)) : a >> (b & 63);
    case BITANDOP: case ASSIGNAND: return a & b;
    case BITOROP: case ASSIGNOR: return a | b;
    case XOROP: case ASSIGNXOR: return a ^ b;
    default: fail("operator", node); return 0;
    }
}

/* p + k on a pointer scales k by the element size */
static i64 ptr_step(expr_node *ptr) { return elem_cells(ptr->type, ptr->structure); }

static i64 rv(expr_node *e, Frame *f) {
    if (!e || err_set) return 0;
    if (++steps > step_limit) { timed_out = 1; fail("timeout", e->node_i); return 0; }
    const int n = e->node_i;
    switch (e->operator) {
    case CONSTANT:
        if (!e->constant) { fail("constant", n); return 0; }
        if (e->constant->const_type & (TYPE_FLOAT | TYPE_DOUBLE | TYPE_STRING)) { fail("constant type", n); return 0; }
        return conv((i64)e->constant->ivalue, e->type ? e->type : e->constant->const_type);
    case IDENTIFIER: {
        const id_struct *id = e->identifier;
        if (id->type & TYPE_FUNCTION) { fail("function value", n); return 0; }
        i64 a = var_addr(id, f, n);
        if (by_address(id->type)) return a;
        return load(a, n);
    }
    case ARRAY: case FIELD: case PFIELD: {
        i64 a = lv(e, f);
        if (by_address(e->type)) return a;
        return load(a, n);
    }
    case POINTSTO: {
        i64 a = rv(e->left, f);
        if (by_address(e->type)) return a;
        return load(a, n);
    }
    case ADDRESSOF:
        return lv(e->left, f);
    case ASSIGN: {
        i64 a = lv(e->left, f);
        if (e->left->type & TYPE_STRUCT) { /* struct copy */
            i64 src = rv(e->right, f);
            int k = cells(e->left->type, e->left->structure);
            if (!valid(a) || !valid(a + k - 1) || !valid(src) || !valid(src + k - 1)) { fail("bad struct copy", n); return 0; }
            memmove(mem + a, mem + src, sizeof(i64) * (size_t)k);
            return a;
        }
        i64 v = conv(rv(e->right, f), e->left->type);
        store(a, v, n);
        return v;
    }
    case ASSIGNADD: case ASSIGNSUB: case ASSIGNMUL: case ASSIGNDIV: case ASSIGNMOD:
    case ASSIGNLSH: case ASSIGNRSH: case ASSIGNAND: case ASSIGNOR: case ASSIGNXOR: {
        i64 a = lv(e->left, f);
        i64 old = load(a, n);
        i64 b = rv(e->right, f);
        if (is_ptr(e->left->type) && (e->operator == ASSIGNADD || e->operator == ASSIGNSUB)) b *= ptr_step(e->left);
        i64 v = conv(arith(e->operator, old, b, e->left->type, e->left->type, n), e->left->type);
        store(a, v, n);
        return v;
    }
    case PREINC: case PREDEC: case POSTINC: case POSTDEC: {
        i64 a = lv(e->left, f);
        i64 old = load(a, n);
        i64 d = is_ptr(e->left->type) ? ptr_step(e->left) : 1;
        i64 v = conv((e->operator == PREINC || e->operator == POSTINC) ? old + d : old - d, e->left->type);
        store(a, v, n);
        return (e->operator == PREINC || e->operator == PREDEC) ? v : old;
    }
    case PLUSOP: case MINUSOP: {
        i64 a = rv(e->left, f), b = rv(e->right, f);
        type_t tl = e->left->type, tr = e->right->type;
        if (is_ptr(tl) && is_ptr(tr) && e->operator == MINUSOP) return (a - b) / ptr_step(e->left);
        if (is_ptr(tl)) return e->operator == PLUSOP ? a + b * ptr_step(e->left) : a - b * ptr_step(e->left);
        if (is_ptr(tr)) return a * ptr_step(e->right) + b;
        return conv(arith(e->operator, conv(a, e->type), conv(b, e->type), e->type, tl, n), e->type);
    }
    case MULOP: case DIVOP: case MODOP: case BITANDOP: case BITOROP: case XOROP: {
        i64 a = conv(rv(e->left, f), e->type), b = conv(rv(e->right, f), e->type);
        return conv(arith(e->operator, a, b, e->type, e->left->type, n), e->type);
    }
    case LSHIFT: case RSHIFT: {
        i64 a = conv(rv(e->left, f), e->type), b = rv(e->right, f);
        return conv(arith(e->operator, a, b, e->type, e->type, n), e->type);
    }
    case EQUOP: case UNEQUOP: case GTOP: case GEOP: case LTOP: case LEOP: {
        i64 a = rv(e->left, f), b = rv(e->right, f);
        int u = is_unsigned(e->left->type) || is_unsigned(e->right->type);
        int r;
        switch (e->operator) {
        case EQUOP: r = a == b; break;
        case UNEQUOP: r = a != b; break;
        case GTOP: r = u ? (u64)a > (u64)b : a > b; break;
        case GEOP: r = u ? (u64)a >= (u64)b : a >= b; break;
        case LTOP: r = u ? (u64)a < (u64)b : a < b; break;
        default: r = u ? (u64)a <= (u64)b : a <= b; break;
        }
        return r;
    }
    case ANDOP: return rv(e->left, f) ? rv(e->right, f) != 0 : 0;
    case OROP: return rv(e->left, f) ? 1 : rv(e->right, f) != 0;
    case NOTOP: return !rv(e->left, f);
    case NEGOP: return conv(-rv(e->left, f), e->type);
    case POSOP: return rv(e->left, f);
    case CMPLOP: return conv(~rv(e->left, f), e->type);
    case TYPECAST: case STYPECAST: case VTYPECAST:
        return conv(rv(e->left, f), e->type);
    case COMMA:
        rv(e->left, f);
        return rv(e->right, f);
    case SELECT: {
        expr_list *l = e->expression_list;
        if (!l || !l->next) { fail("select", n); return 0; }
        return rv(e->left, f) ? rv(l->expression, f) : rv(l->next->expression, f);
    }
    case FUNCALL: {
        const id_struct *id = e->left ? e->left->identifier : NULL;
        if (!id || !(id->type & TYPE_FUNCTION) || !id->subdata) { fail("call", n); return 0; }
        return conv(call(id->subdata, e->expression_list, f, n), e->type);
    }
    default:
        fail("unsupported operator", n);
        return 0;
    }
}

/* ---------------------------------------------------------------- instructions */
typedef enum { NORMAL, BREAK, CONTINUE, RETURN } Flow;
typedef struct { Flow flow; instr_node *target; i64 value; } Status;

static Status exec_seq(instr_node *i, Frame *f);

static Status ok(void) { Status s = {NORMAL, NULL, 0}; return s; }

/* A loop body ended with break or continue aimed at this loop? */
static int loop_flow(Status *s, instr_node *loop, int *stop) {
    *stop = 0;
    if (s->flow == BREAK && s->target == loop) { *stop = 1; *s = ok(); return 1; }
    if (s->flow == CONTINUE && s->target == loop) { *s = ok(); return 1; }
    if (s->flow != NORMAL) { *stop = 1; return 0; }
    return 1;
}

static Status exec_one(instr_node *i, Frame *f) {
    Status s = ok();
    if (++steps > step_limit) { timed_out = 1; fail("timeout", i->node_i); return s; }
    switch (i->type) {
    case EXPRESSION:
        if (i->expression) rv(i->expression, f);
        return s;
    case IF_BRANCH:
        return rv(i->expression, f) ? exec_seq(i->instruction, f) : exec_seq(i->tail_instruction, f);
    case WHILE_LOOP:
        while (!err_set && rv(i->expression, f)) {
            int stop;
            s = exec_seq(i->instruction, f);
            int mine = loop_flow(&s, i, &stop);
            if (stop) return mine ? ok() : s;
        }
        return ok();
    case DO_LOOP:
        do {
            int stop;
            s = exec_seq(i->instruction, f);
            int mine = loop_flow(&s, i, &stop);
            if (stop) return mine ? ok() : s;
        } while (!err_set && rv(i->expression, f));
        return ok();
    case FOR_LOOP: {
        expr_list *init = i->ex_list;
        expr_list *cond = init ? init->next : NULL;
        expr_list *step = cond ? cond->next : NULL;
        if (init && init->expression) rv(init->expression, f);
        while (!err_set && (!cond || !cond->expression || rv(cond->expression, f))) {
            int stop;
            s = exec_seq(i->tail_instruction, f);
            int mine = loop_flow(&s, i, &stop);
            if (stop) return mine ? ok() : s;
            if (step && step->expression) rv(step->expression, f);
        }
        return ok();
    }
    case SELECT_BRANCH: {
        i64 v = rv(i->expression, f);
        instr_node *start = NULL;
        for (instr_list *l = i->target_list; l; l = l->next)
            if (l->constant && conv((i64)l->constant->ivalue, i->expression->type) == v) { start = l->instruction; break; }
        if (!start) start = i->tail_instruction;
        if (!start) return ok();
        s = exec_seq(start, f);
        if (s.flow == BREAK && s.target == i) return ok();
        return s;
    }
    case S_BREAK: s.flow = BREAK; s.target = i->target; return s;
    case S_CONTINUE: s.flow = CONTINUE; s.target = i->target; return s;
    case S_RETURN:
        s.flow = RETURN;
        s.value = i->expression ? rv(i->expression, f) : 0;
        return s;
    default:
        fail("unsupported instruction", i->node_i);
        return s;
    }
}

static Status exec_seq(instr_node *i, Frame *f) {
    for (; i && !err_set; i = i->next) {
        Status s = exec_one(i, f);
        if (s.flow != NORMAL) return s;
    }
    return ok();
}

static int depth;
static i64 call(sub_struct *sub, expr_list *args, Frame *caller, int node) {
    if (sub->library || !sub->sub_first) { fail("library call", node); return 0; }
    if (++depth > 64) { fail("recursion", node); depth--; return 0; }
    if (sub->items >= 0x10000) { fail("frame", node); depth--; return 0; }
    Frame *f = malloc(sizeof *f);
    f->sub = sub;
    i64 argv_[256];
    int argc = 0;
    for (expr_list *l = args; l && argc < 256; l = l->next) argv_[argc++] = rv(l->expression, caller);
    for (int k = 0; k < sub->items; k++) f->base[k] = alloc_cells(cells(sub->locals[k].type, sub->locals[k].structure));
    for (int k = 1; k <= sub->params && k <= argc; k++) {
        record *p = &sub->locals[k];
        if (p->type & TYPE_ARRAY) f->base[k] = (int)argv_[k - 1]; /* array parameter: the caller's array */
        else if (p->type & TYPE_STRUCT) { /* struct parameter: a copy */
            int c = cells(p->type, p->structure);
            if (!valid(argv_[k - 1]) || !valid(argv_[k - 1] + c - 1)) { fail("bad struct argument", node); break; }
            memmove(mem + f->base[k], mem + argv_[k - 1], sizeof(i64) * (size_t)c);
        } else mem[f->base[k]] = conv(argv_[k - 1], p->type);
    }
    Status s = exec_seq(sub->sub_first, f);
    i64 r = s.flow == RETURN ? s.value : 0;
    free(f);
    depth--;
    return r;
}

/* ---------------------------------------------------------------- driver */
static u64 rng;
static u64 next_rand(void) {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
}
static i64 rand_value(void) {
    switch (next_rand() % 4) {
    case 0: return (i64)(next_rand() % 3);              /* 0, 1, 2: flags and cases */
    case 1: return (i64)(next_rand() % 17) - 8;         /* small, either sign */
    case 2: return (i64)(next_rand() % 256);            /* byte range */
    default: return (i64)(int)(unsigned)next_rand();    /* any 32-bit value */
    }
}

static void init_global(int g) {
    static_record *r = &globals[g];
    int n = cells(r->type, r->structure);
    global_base[g] = alloc_cells(n);
    expr_node *iv = r->init_value;
    if (!iv) return;
    if (iv->operator == CONSTANT && iv->constant) { mem[global_base[g]] = conv((i64)iv->constant->ivalue, r->type); return; }
    if (iv->operator == AGGREGATE) {
        int k = 0;
        for (expr_list *l = iv->expression_list; l && k < n; l = l->next, k++)
            if (l->expression && l->expression->operator == CONSTANT) mem[global_base[g] + k] = (i64)l->expression->constant->ivalue;
            else { fail("global initializer", g); return; }
        return;
    }
    fail("global initializer", g);
}

#define BUF_CELLS 4096

static expr_list *const_arg(expr_list **tail, i64 v) {
    const_struct *c = calloc(1, sizeof *c);
    expr_node *leaf = calloc(1, sizeof *leaf);
    expr_list *l = calloc(1, sizeof *l);
    if (!c || !leaf || !l) { perror("calloc"); exit(2); }
    c->const_type = TYPE_LONGLONG;
    c->ivalue = (u64)v;
    leaf->operator = CONSTANT;
    leaf->type = TYPE_LONGLONG;
    leaf->constant = c;
    l->expression = leaf;
    *tail = l;
    return l;
}

/* One run of subroutine `sub` on the inputs of `seed`; prints its result line. */
static void run(sub_struct *sub, int seed) {
    rng = 0x9E3779B97F4A7C15ULL ^ (u64)seed * 0x100000001B3ULL;
    for (int w = 0; w < 4; w++) next_rand();
    mem_top = 1;
    err_set = 0;
    timed_out = 0;
    steps = 0;
    depth = 0;
    for (int g = 0; g < cur_glob_index; g++) init_global(g);
    /* arguments: scalars get random values; pointers, arrays and structs point to
       random cells (at least BUF_CELLS, and 128 elements, for pointers and arrays) */
    int nparams = sub->params < 255 ? sub->params : 255;
    int bufs[256], bufn[256];
    expr_list *args = NULL, **tail = &args;
    for (int k = 1; k <= nparams; k++) {
        record *p = &sub->locals[k];
        i64 v;
        bufs[k] = bufn[k] = 0;
        if (p->type & (TYPE_POINTER | TYPE_ARRAY | TYPE_STRUCT)) {
            int n = (p->type & TYPE_STRUCT) ? cells(p->type, p->structure) : BUF_CELLS;
            if (!(p->type & TYPE_STRUCT) && 128 * elem_cells(p->type, p->structure) > n) n = 128 * elem_cells(p->type, p->structure);
            type_t et = (p->type & TYPE_STRUCT) || !p->structure ? TYPE_INT : p->structure->s_pointer.type;
            if (et & (TYPE_STRUCT | TYPE_ARRAY | TYPE_POINTER)) et = TYPE_INT;
            bufs[k] = alloc_cells(n);
            bufn[k] = n;
            for (int c = 0; c < n; c++) mem[bufs[k] + c] = conv(rand_value(), et);
            v = bufs[k];
        } else {
            v = conv(rand_value(), p->type);
        }
        tail = &const_arg(tail, v)->next;
    }
    i64 ret = call(sub, args, NULL, -1);
    /* observable state: return value, argument buffers, globals */
    u64 h = 1469598103934665603ULL;
#define MIX(x) do { h ^= (u64)(x); h *= 1099511628211ULL; } while (0)
    MIX(ret);
    for (int k = 1; k <= nparams; k++)
        for (int c = 0; c < bufn[k]; c++) MIX(mem[bufs[k] + c]);
    for (int g = 0; g < cur_glob_index; g++) {
        int n = cells(globals[g].type, globals[g].structure);
        for (int c = 0; c < n; c++) MIX(mem[global_base[g] + c]);
    }
    if (timed_out) printf("%s seed %d timeout\n", sub->name, seed);
    else if (err_set) printf("%s seed %d error:%s\n", sub->name, seed, err_reason);
    else printf("%s seed %d ok ret %lld state %016llx steps %lld\n", sub->name, seed, ret, h, steps);
    while (args) {
        expr_list *nx = args->next;
        free(args->expression->constant);
        free(args->expression);
        free(args);
        args = nx;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: ir_interp file.ir [runs] [first_seed] [all]\n");
        return 2;
    }
    int runs = argc > 2 ? atoi(argv[2]) : 100;
    int first = argc > 3 ? atoi(argv[3]) : 1;
    int all = argc > 4 && strcmp(argv[4], "all") == 0;
    if (load_intermediate(argv[1])) { fprintf(stderr, "cannot load %s\n", argv[1]); return 2; }
    mem = malloc(sizeof(i64) * MEM_CELLS);
    if (!mem) { perror("malloc"); return 2; }
    printf("\n");
    for (int s = 0; s < subroutine_number; s++) {
        sub_struct *sub = subroutines[s];
        if (!sub || sub->library || !sub->sub_first) continue;
        if (!all && s != mainfuncindex) continue;
        for (int r = 0; r < runs; r++) run(sub, first + r);
    }
    return 0;
}

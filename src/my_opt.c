/* my_opt.c - optimizer for the intermediate representation (IR) of the CCC
 * high-level-synthesis toolchain (C front end translator, inter_library).
 *
 *   my_opt input.ir [-iterative]    reads input.ir, optimizes it, writes result.ir
 *
 * The CCC IR is a syntax tree. A subroutine is a list of instruction nodes
 * linked by `next`; an if keeps its branches in `instruction` / `tail_instruction`,
 * a while or do loop its body in `instruction`, a for loop its three expressions
 * in `ex_list` and its body in `tail_instruction`. A switch body is a single
 * list, as in C: the case labels in `target_list` and the default in
 * `tail_instruction` point into it. break and continue name the loop or switch
 * they leave or restart; goto names its target statement. Each of these fields
 * is valid only for its instruction type (in other instructions it holds
 * leftover data), so every walk below dispatches on the instruction type. Local
 * variables are referenced with rec_index = -k for entry k of the subroutine's
 * locals table; globals with rec_index >= 0.
 *
 * Analyses (Aho, Lam, Sethi, Ullman, "Compilers", 2nd ed., chapter 9)
 *   - control-flow graph of the subroutine: one node per instruction, three for a
 *     for loop (initialization, condition, step)
 *   - dominators (iterative bit-vector algorithm, section 9.6.1)
 *   - natural loops (back edges whose head dominates their tail, section 9.6.6)
 *   - region hierarchy (section 9.7, Algorithm 9.52): statements are the leaf
 *     regions; the loop regions are ordered from the innermost outwards, and
 *     each one's summary, the set of variables it may define, is built from the
 *     summaries of the regions inside it and its own statements
 *   - constant propagation, two ways: region-based (non-iterative, using the
 *     region summaries) and iterative (sections 9.3-9.4, on the control-flow
 *     graph until nothing changes). Both always run and are compared: every
 *     constant the region-based analysis finds must be found, with the same
 *     value, by the iterative one. Option -iterative makes the iterative result
 *     the one applied; by default the region-based one is.
 *
 * Transformations
 *   1. constant propagation with constant folding and algebraic simplification
 *      (x+0, x*1, x*0, ...)
 *   2. loop-invariant code motion: an integer expression the loop cannot change
 *      is computed once, into a new temporary, before the loop
 *   3. copy propagation: after x = y, later uses of x become y
 *   4. common-subexpression elimination: in x = e; ... z = e, the second becomes z = x
 *   5. dead-code elimination: an assignment to a variable that is never read,
 *      with no side effect on the right-hand side, becomes an empty instruction
 *
 * Safety
 *   - facts are kept only for local scalar integer variables whose address is
 *     never taken (no &x anywhere in the subroutine), other than the function result;
 *     such variables cannot change through pointers, arrays or calls,
 *     so stores and calls do not invalidate them
 *   - variables are rewritten only where they are read: never on the left of an
 *     assignment, under ++/--, or under address-of
 *   - folding covers integer + - * / % << >> & | ^ and unary minus, only when the
 *     result fits in 32 bits, and / % << >> & | ^ only for non-negative operands
 *   - facts are discarded at goto targets, and a loop or switch that a goto can
 *     enter from outside has no facts at its exit
 *   - code motion moves only expressions that cannot fail or have a side effect
 *     (no division, memory access or call), and never before a loop that is a
 *     jump target
 *   - nodes are rewritten in place; a removed instruction becomes an empty
 *     expression instruction, a form the front end itself produces; the only new
 *     nodes are the instructions code motion inserts, whose temporaries are
 *     added to the locals table and to the IR's name table (names_size)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "csensetypes.h"
#include "intermediate.h"
#include "irloadstore.h"

extern int subroutine_number;
extern int e_node_number;
extern int i_node_number;
extern int typestruct_number;
extern int cur_typename_index;
extern int names_size;
extern int file_args;
extern char **file_names;
extern sub_struct *subroutines[];
extern int cur_glob_index;
extern static_record globals[];
extern int mainfuncindex;

int my_opt_verbose = 1;

typedef struct {
    int instructions, cfg_edges, back_edges, loop_regions, loop_statements;
    int constants_propagated, folded, simplified, copies_propagated, cse, dead_removed, hoisted, temps;
    int iterative_passes, iterative_gave_up, cmp_region, cmp_iterative, cmp_region_only, cmp_disagree, skipped;
} OptStats;
static OptStats g;

static sub_struct *S; /* subroutine being optimized */

/* ======================================================================
 * Variables
 * ====================================================================== */
#define SCALAR_INT (TYPE_CHAR | TYPE_SHORT | TYPE_INT | TYPE_LONG | TYPE_LONGLONG | TYPE_ENUM)
#define NOT_SCALAR (TYPE_POINTER | TYPE_ARRAY | TYPE_UNION | TYPE_STRUCT | TYPE_FUNCTION | TYPE_FLOAT | TYPE_DOUBLE | TYPE_STRING)

static int is_ident(const expr_node *e) { return e && e->operator == IDENTIFIER && e->identifier; }

/* Locals whose address the subroutine takes (&x). The front end does not fill in
 * record.address_used in the stored IR, so optimize_subroutine computes it. */
static unsigned char *addr_taken;

/* Local scalar integer variable whose address is never taken, other than the result slot. */
static int tracked(const id_struct *id) {
    if (!id || (id->type & TYPE_FUNCTION)) return 0;
    int k = -id->rec_index;
    if (k <= 0 || k >= S->items) return 0;
    const record *r = &S->locals[k];
    if (r->address_used || !addr_taken || addr_taken[k]) return 0;
    if (!(id->type & SCALAR_INT) || (id->type & NOT_SCALAR)) return 0;
    if (!(r->type & SCALAR_INT) || (r->type & NOT_SCALAR)) return 0;
    return 1;
}

/* Index k of a tracked variable read or written by an identifier node, or 0. */
static int var_of(const expr_node *e) { return (is_ident(e) && tracked(e->identifier)) ? -e->identifier->rec_index : 0; }

/* ======================================================================
 * Expressions
 * ====================================================================== */
static int is_assign_op(oper_t op) { return op >= ASSIGNADD && op <= ASSIGN; }
static int is_incdec(oper_t op) { return op == PREINC || op == PREDEC || op == POSTINC || op == POSTDEC; }
static int has_list(oper_t op) { return op == FUNCALL || op == SELECT || op == AGGREGATE; }
static int is_leaf(oper_t op) { return op == CONSTANT || op == IDENTIFIER; }

/* Calls f on every child slot of e; lvalue is 1 for an assignment target, the
 * operand of ++/-- or &, and the callee of a call. */
typedef void (*slot_fn)(expr_node **slot, int lvalue, void *ctx);

static void for_children(expr_node *e, slot_fn f, void *ctx) {
    if (!e || is_leaf(e->operator)) return;
    if (has_list(e->operator)) {
        if (e->operator != AGGREGATE && e->left) f(&e->left, e->operator == FUNCALL, ctx);
        for (expr_list *l = e->expression_list; l; l = l->next) f(&l->expression, 0, ctx);
        return;
    }
    int lhs = is_assign_op(e->operator) || is_incdec(e->operator) || e->operator == ADDRESSOF;
    if (e->left) f(&e->left, lhs, ctx);
    if (e->right) f(&e->right, 0, ctx);
}

/* Visits every identifier node that is read. */
typedef void (*use_fn)(expr_node *ident, void *ctx);
typedef struct { use_fn f; void *ctx; } UseWalk;

static void walk_slot(expr_node **slot, int lvalue, void *vw) {
    UseWalk *w = vw;
    expr_node *e = *slot;
    if (!e) return;
    if (lvalue) {
        /* the target is not read, but its sub-expressions (index, pointer) are */
        if (!is_ident(e)) for_children(e, walk_slot, w);
        return;
    }
    if (is_ident(e)) w->f(e, w->ctx);
    else for_children(e, walk_slot, w);
}

static void walk_uses(expr_node *e, use_fn f, void *ctx) {
    if (!e) return;
    if (is_ident(e)) { f(e, ctx); return; }
    UseWalk w = {f, ctx};
    for_children(e, walk_slot, &w);
}

/* Tracked variables written by an expression, and its other side effects.
 * `overflow` means more variables are written than fit in defs; callers then
 * assume that every tracked variable may be written. */
#define MAX_DEFS 256
typedef struct { int defs[MAX_DEFS]; int n; int calls; int other_stores; int overflow; } Effects;
#define NO_EFFECTS {{0}, 0, 0, 0, 0}

static void add_def(Effects *fx, int v) {
    for (int i = 0; i < fx->n; i++)
        if (fx->defs[i] == v) return;
    if (fx->n < MAX_DEFS) fx->defs[fx->n++] = v;
    else fx->overflow = 1;
}

static void effects_of(const expr_node *e, Effects *fx) {
    if (!e || is_leaf(e->operator)) return;
    if (e->operator == FUNCALL) fx->calls = 1;
    if (is_assign_op(e->operator) || is_incdec(e->operator)) {
        int v = var_of(e->left);
        if (v) add_def(fx, v);
        else fx->other_stores = 1;
    }
    if (has_list(e->operator)) {
        if (e->operator != AGGREGATE) effects_of(e->left, fx);
        for (expr_list *l = e->expression_list; l; l = l->next) effects_of(l->expression, fx);
    } else {
        effects_of(e->left, fx);
        effects_of(e->right, fx);
    }
}

static int side_effects(const expr_node *e) {
    Effects fx = NO_EFFECTS;
    effects_of(e, &fx);
    return fx.n || fx.calls || fx.other_stores || fx.overflow;
}

typedef struct { int v; int found; } FindCtx;
static void find_use(expr_node *id, void *c) {
    FindCtx *f = c;
    if (var_of(id) == f->v) f->found = 1;
}
static int expr_uses_var(expr_node *e, int v) {
    FindCtx f = {v, 0};
    walk_uses(e, find_use, &f);
    return f.found;
}

static int int_kind(const const_struct *c) { return c && (c->const_type & SCALAR_INT) && !(c->const_type & TYPE_UNSIGNED); }

static int const_equal(const const_struct *a, const const_struct *b) {
    return int_kind(a) && int_kind(b) && a->ivalue == b->ivalue;
}

/* Pure integer expression over tracked variables and constants. */
static int pure_expr(const expr_node *e) {
    if (!e) return 0;
    if (e->operator == CONSTANT) return int_kind(e->constant);
    if (e->operator == IDENTIFIER) return var_of(e) != 0;
    if (!(e->type & SCALAR_INT) || (e->type & NOT_SCALAR)) return 0;
    switch (e->operator) {
    case PLUSOP: case MINUSOP: case MULOP: case DIVOP: case MODOP: case LSHIFT: case RSHIFT:
    case BITANDOP: case BITOROP: case XOROP:
        return pure_expr(e->left) && pure_expr(e->right);
    case NEGOP:
        return pure_expr(e->left);
    default:
        return 0;
    }
}

static int expr_equal(const expr_node *a, const expr_node *b) {
    if (a->operator != b->operator) return 0;
    if (a->operator == CONSTANT) return const_equal(a->constant, b->constant);
    if (a->operator == IDENTIFIER) return var_of(a) == var_of(b);
    if ((a->left == NULL) != (b->left == NULL) || (a->right == NULL) != (b->right == NULL)) return 0;
    return (!a->left || expr_equal(a->left, b->left)) && (!a->right || expr_equal(a->right, b->right));
}

/* ----- in-place rewriting (fresh copies, never shared structures) ----- */
static const_struct *new_int_const(long long v) {
    const_struct *c = calloc(1, sizeof *c);
    if (!c) { perror("calloc"); exit(1); }
    c->const_type = TYPE_INT;
    c->ivalue = (unsigned long long)v;
    return c;
}

static void drop_children(expr_node *e) {
    if (is_leaf(e->operator)) return;
    if (has_list(e->operator)) return; /* never rewritten */
    if (e->left) delete_expression(e->left);
    if (e->right) delete_expression(e->right);
    e->right = NULL;
}

static void become_constant(expr_node *e, long long v) {
    drop_children(e);
    e->operator = CONSTANT;
    e->constant = new_int_const(v);
}

static void become_identifier(expr_node *e, const id_struct *id) {
    id_struct *copy = malloc(sizeof *copy);
    if (!copy) { perror("malloc"); exit(1); }
    *copy = *id; /* before drop_children: id may belong to a child */
    drop_children(e);
    e->operator = IDENTIFIER;
    e->identifier = copy;
}

/* ----- constant folding and algebraic simplification ----- */
static int in_int32(long long v) { return v >= -2147483647LL - 1 && v <= 2147483647LL; }

static int int_const(const expr_node *e, long long *v) {
    if (!e || e->operator != CONSTANT || !int_kind(e->constant)) return 0;
    *v = (long long)e->constant->ivalue;
    return in_int32(*v);
}

/* Nodes whose value folding may compute: signed integer arithmetic. */
static int foldable_type(const expr_node *e) {
    return (e->type & SCALAR_INT) && !(e->type & (NOT_SCALAR | TYPE_UNSIGNED));
}

/* a op b, when the result is the same as C's on 32-bit int and fits in it. */
static int compute(oper_t op, long long a, long long b, long long *r) {
    switch (op) {
    case PLUSOP: *r = a + b; break;
    case MINUSOP: *r = a - b; break;
    case MULOP: *r = a * b; break;
    case DIVOP: if (b <= 0 || a < 0) return 0; *r = a / b; break;
    case MODOP: if (b <= 0 || a < 0) return 0; *r = a % b; break;
    case LSHIFT: if (a < 0 || b < 0 || b > 30) return 0; *r = a << b; break;
    case RSHIFT: if (a < 0 || b < 0 || b > 30) return 0; *r = a >> b; break;
    case BITANDOP: if (a < 0 || b < 0) return 0; *r = a & b; break;
    case BITOROP: if (a < 0 || b < 0) return 0; *r = a | b; break;
    case XOROP: if (a < 0 || b < 0) return 0; *r = a ^ b; break;
    case NEGOP: *r = -a; break;
    default: return 0;
    }
    return in_int32(*r);
}

/* e takes the place of its operand x, which must have e's type: x's operator and
 * children move into e, so e keeps its position in the tree. */
static void become_operand(expr_node *e, expr_node *x) {
    expr_node *other = x == e->left ? e->right : e->left;
    if (other) delete_expression(other);
    e->operator = x->operator;
    e->structure = x->structure;
    e->attribute = x->attribute;
    e->left = x->left; /* the unions: left / constant / identifier, right / expression_list */
    e->right = x->right;
    if (!is_leaf(e->operator)) {
        if (has_list(e->operator)) {
            if (e->left) e->left->parent = e;
            for (expr_list *l = e->expression_list; l; l = l->next) l->expression->parent = e;
        } else {
            if (e->left) e->left->parent = e;
            if (e->right) e->right->parent = e;
        }
    }
    /* x itself is not freed: the library allocates nodes, and its contents now belong to e */
}

/* Identities with one constant operand c and an operand x of the node's own type:
 * x+0 0+x x-0 x*1 1*x x/1 x<<0 x>>0 x|0 0|x x^0 0^x become x; x*0 0*x x&0 0&x
 * become 0 when x has no side effect. */
static int simplify(expr_node *e) {
    if (!e->left || !e->right) return 0;
    long long c;
    expr_node *x;
    int const_left = int_const(e->left, &c);
    if (const_left) x = e->right;
    else if (int_const(e->right, &c)) x = e->left;
    else return 0;
    if (x->type != e->type) return 0;
    int to_x = 0, to_zero = 0;
    switch (e->operator) {
    case PLUSOP: case BITOROP: case XOROP: to_x = c == 0; break;
    case MINUSOP: case DIVOP: case LSHIFT: case RSHIFT: to_x = !const_left && c == (e->operator == DIVOP); break;
    case MULOP: to_x = c == 1; to_zero = c == 0; break;
    case BITANDOP: to_zero = c == 0; break;
    default: break;
    }
    if (to_zero && !side_effects(x)) { become_constant(e, 0); return 1; }
    if (!to_x) return 0;
    become_operand(e, x);
    return 1;
}

static void fold(expr_node *e) {
    if (!e || is_leaf(e->operator) || has_list(e->operator) || !foldable_type(e)) return;
    long long a, b = 0, r;
    if (int_const(e->left, &a) && (e->operator == NEGOP || int_const(e->right, &b)) && compute(e->operator, a, b, &r)) {
        become_constant(e, r);
        g.folded++;
    } else if (simplify(e)) {
        g.simplified++;
    }
}

static void fold_tree(expr_node *e);
static void fold_slot(expr_node **slot, int lvalue, void *ctx) {
    (void)lvalue; (void)ctx;
    fold_tree(*slot);
}
static void fold_tree(expr_node *e) {
    if (!e || is_leaf(e->operator)) return;
    for_children(e, fold_slot, NULL);
    fold(e);
}

/* ======================================================================
 * Instruction walks
 * ====================================================================== */
typedef void (*instr_fn)(instr_node *i, void *ctx);

/* A switch body is one statement list, as in C; its case labels and default
 * point into that list. The body starts at the label no other label reaches. */
static int reaches(const instr_node *from, const instr_node *to) {
    for (; from; from = from->next)
        if (from == to) return 1;
    return 0;
}

static instr_node *switch_body(instr_node *sw) {
    instr_node *labels[512];
    int n = 0;
    for (instr_list *l = sw->target_list; l && n < 511; l = l->next)
        if (l->instruction) labels[n++] = l->instruction;
    if (sw->tail_instruction) labels[n++] = sw->tail_instruction;
    for (int a = 0; a < n; a++) {
        int first = 1;
        for (int b = 0; b < n && first; b++)
            if (labels[b] != labels[a] && reaches(labels[b], labels[a])) first = 0;
        if (first) return labels[a];
    }
    return n ? labels[0] : NULL;
}

static void for_each_instr(instr_node *i, instr_fn f, void *ctx) {
    for (; i; i = i->next) {
        f(i, ctx);
        switch (i->type) {
        case IF_BRANCH:
            for_each_instr(i->instruction, f, ctx);
            for_each_instr(i->tail_instruction, f, ctx);
            break;
        case WHILE_LOOP: case DO_LOOP:
            for_each_instr(i->instruction, f, ctx);
            break;
        case FOR_LOOP:
            for_each_instr(i->tail_instruction, f, ctx);
            break;
        case SELECT_BRANCH:
            for_each_instr(switch_body(i), f, ctx);
            break;
        default:
            break;
        }
    }
}

/* Applies f to every expression owned by one instruction. */
static void for_each_expr(instr_node *i, void (*f)(expr_node *, void *), void *ctx) {
    switch (i->type) {
    case EXPRESSION: case S_RETURN: case IF_BRANCH: case WHILE_LOOP: case DO_LOOP: case SELECT_BRANCH:
        if (i->expression) f(i->expression, ctx);
        break;
    case FOR_LOOP:
        for (expr_list *l = i->ex_list; l; l = l->next)
            if (l->expression) f(l->expression, ctx);
        break;
    default:
        break;
    }
}

/* Join points inside a statement list: goto targets and case labels. (break and
 * continue name their loop or switch statement, whose summary covers them.)
 * If the tables overflow, every statement counts as a join point. */
#define MAX_TARGETS 8192
static instr_node *gotos[MAX_TARGETS], *labels[MAX_TARGETS];
static int ngotos, nlabels, targets_overflow;

static void add_to(instr_node **set, int *n, instr_node *t) {
    if (!t) return;
    if (*n < MAX_TARGETS) set[(*n)++] = t;
    else targets_overflow = 1;
}

static void collect_target(instr_node *i, void *ctx) {
    (void)ctx;
    if (i->type == S_GOTO) add_to(gotos, &ngotos, i->target);
    if (i->type == SELECT_BRANCH) {
        for (instr_list *l = i->target_list; l; l = l->next) add_to(labels, &nlabels, l->instruction);
        add_to(labels, &nlabels, i->tail_instruction);
    }
}

static int in_set(instr_node *const *set, int n, const instr_node *i) {
    if (targets_overflow) return 1;
    for (int k = 0; k < n; k++)
        if (set[k] == i) return 1;
    return 0;
}
static int is_goto_target(const instr_node *i) { return in_set(gotos, ngotos, i); }
static int is_target(const instr_node *i) { return is_goto_target(i) || in_set(labels, nlabels, i); }

/* Is i a case label or the default of switch sw? */
static int is_label_of(const instr_node *sw, const instr_node *i) {
    for (instr_list *l = sw->target_list; l; l = l->next)
        if (l->instruction == i) return 1;
    return sw->tail_instruction == i;
}

/* Does the statement i, with its nested statements, contain a goto target? Then
 * control can enter it from outside, and its summary does not describe its exit. */
typedef struct { int found; } EntryCtx;
static void find_goto_target(instr_node *i, void *vc) {
    if (is_goto_target(i)) ((EntryCtx *)vc)->found = 1;
}
static int entered_by_goto(instr_node *i) {
    if (ngotos == 0 && !targets_overflow) return 0;
    EntryCtx c = {0};
    instr_node *saved = i->next;
    i->next = NULL;
    for_each_instr(i, find_goto_target, &c);
    i->next = saved;
    return c.found;
}

/* ======================================================================
 * Control-flow graph, dominators, natural loops, region hierarchy
 * ====================================================================== */
/* One node per instruction; a for loop has three: its initialization, its
 * condition (the loop head) and its step. */
#define MAXN 8192
#define MAXE 65536
enum { PART_MAIN, PART_INIT, PART_STEP };
static instr_node *cfg_node[MAXN];
static int cfg_part[MAXN];
static int ncfg, cfg_overflow;
static int edge_from[MAXE], edge_to[MAXE], nedges;
static int after_of[MAXN]; /* for a loop or switch: the node control reaches when it ends */
static int cont_of[MAXN];  /* for a loop: the node continue goes to */

static int cfg_part_id(const instr_node *i, int part) {
    for (int k = 0; k < ncfg; k++)
        if (cfg_node[k] == i && cfg_part[k] == part) return k;
    return -1;
}
static int cfg_id(const instr_node *i) { return cfg_part_id(i, PART_MAIN); }

static void add_node(instr_node *i, int part) {
    if (ncfg >= MAXN - 1) { cfg_overflow = 1; return; }
    cfg_node[ncfg] = i;
    cfg_part[ncfg] = part;
    ncfg++;
}
static void number_instr(instr_node *i, void *ctx) {
    (void)ctx;
    if (cfg_id(i) >= 0) return;
    add_node(i, PART_MAIN);
    if (i->type == FOR_LOOP) {
        add_node(i, PART_INIT);
        add_node(i, PART_STEP);
    }
}

/* The expression a node evaluates, or NULL. */
static expr_node *node_expr(int k) {
    instr_node *i = cfg_node[k];
    if (!i) return NULL;
    switch (i->type) {
    case EXPRESSION: case S_RETURN: case IF_BRANCH: case WHILE_LOOP: case DO_LOOP: case SELECT_BRANCH:
        return i->expression;
    case FOR_LOOP: {
        expr_list *l = i->ex_list; /* initialization, condition, step */
        if (l && cfg_part[k] != PART_INIT) l = l->next;
        if (l && cfg_part[k] == PART_STEP) l = l->next;
        return l ? l->expression : NULL;
    }
    default:
        return NULL;
    }
}

static void add_edge(int a, int b) {
    if (a < 0 || b < 0) { cfg_overflow = 1; return; }
    if (nedges >= MAXE) { cfg_overflow = 1; return; }
    for (int k = 0; k < nedges; k++)
        if (edge_from[k] == a && edge_to[k] == b) return;
    edge_from[nedges] = a;
    edge_to[nedges] = b;
    nedges++;
}

/* Entry node of a statement list, or `cont` when it is empty. A do loop starts
 * with its body, a for loop with its initialization. */
static int entry_of(instr_node *seq, int cont) {
    if (!seq) return cont;
    if (seq->type == DO_LOOP && seq->instruction) return entry_of(seq->instruction, cfg_id(seq));
    if (seq->type == FOR_LOOP) return cfg_part_id(seq, PART_INIT);
    return cfg_id(seq);
}

/* cont: the node control reaches after the list. break and continue name their
 * loop or switch statement; break leaves it, continue goes to the loop's test
 * (to the step, in a for loop). */
static void build_cfg(instr_node *seq, int cont, int exit_node) {
    for (instr_node *i = seq; i; i = i->next) {
        int me = cfg_id(i);
        int after = i->next ? entry_of(i->next, cont) : cont;
        switch (i->type) {
        case IF_BRANCH:
            add_edge(me, entry_of(i->instruction, after));
            add_edge(me, entry_of(i->tail_instruction, after));
            build_cfg(i->instruction, after, exit_node);
            build_cfg(i->tail_instruction, after, exit_node);
            break;
        case WHILE_LOOP: case DO_LOOP:
            after_of[me] = after;
            cont_of[me] = me;
            add_edge(me, entry_of(i->instruction, me));
            add_edge(me, after);
            build_cfg(i->instruction, me, exit_node);
            break;
        case FOR_LOOP: {
            int init = cfg_part_id(i, PART_INIT), step = cfg_part_id(i, PART_STEP);
            after_of[me] = after;
            cont_of[me] = step;
            add_edge(init, me);
            add_edge(me, entry_of(i->tail_instruction, step));
            add_edge(me, after);
            add_edge(step, me);
            build_cfg(i->tail_instruction, step, exit_node);
            break;
        }
        case SELECT_BRANCH:
            after_of[me] = after;
            for (instr_list *l = i->target_list; l; l = l->next) add_edge(me, entry_of(l->instruction, after));
            add_edge(me, i->tail_instruction ? entry_of(i->tail_instruction, after) : after);
            build_cfg(switch_body(i), after, exit_node);
            break;
        case S_GOTO:
            add_edge(me, i->target ? entry_of(i->target, after) : after);
            break;
        case S_BREAK: {
            int t = i->target ? cfg_id(i->target) : -1;
            add_edge(me, t >= 0 ? after_of[t] : after);
            break;
        }
        case S_CONTINUE: {
            int t = i->target ? cfg_id(i->target) : -1;
            add_edge(me, t >= 0 ? cont_of[t] : after);
            break;
        }
        case S_RETURN:
            add_edge(me, exit_node);
            break;
        default:
            add_edge(me, after);
            break;
        }
    }
}

/* Loop regions of Algorithm 9.52. `members` marks the nodes of the natural loop,
 * `defs` the tracked variables the region may define (the kill set of its
 * constant-propagation transfer function). */
typedef struct { int head; int size; unsigned char *members; unsigned char *defs; } LoopRegion;
#define MAX_REGIONS 1024
static LoopRegion regions[MAX_REGIONS];
static int nregions;

typedef struct { unsigned char *defs; } DefCtx;
static void node_defs(expr_node *e, void *vc) {
    DefCtx *c = vc;
    Effects fx = NO_EFFECTS;
    effects_of(e, &fx);
    for (int k = 0; k < fx.n; k++) c->defs[fx.defs[k]] = 1;
}

static void free_regions(void) {
    for (int r = 0; r < nregions; r++) {
        free(regions[r].members);
        free(regions[r].defs);
    }
    nregions = 0;
}

static int exit_node, entry_node;

/* Builds the CFG and the region hierarchy. Returns 0 when the subroutine is too
 * large for the tables, in which case it is left unoptimized. */
static int analyse_cfg(sub_struct *sub) {
    free_regions();
    ncfg = 0;
    nedges = 0;
    cfg_overflow = 0;
    for_each_instr(sub->sub_first, number_instr, NULL);
    if (ncfg == 0 || cfg_overflow) return 0;
    exit_node = ncfg; /* virtual exit */
    cfg_node[exit_node] = NULL;
    for (int k = 0; k <= exit_node; k++) after_of[k] = cont_of[k] = exit_node;
    build_cfg(sub->sub_first, exit_node, exit_node);
    if (cfg_overflow) return 0;
    const int n = exit_node + 1;
    for (int k = 0; k < ncfg; k++) g.instructions += cfg_part[k] == PART_MAIN;
    g.cfg_edges += nedges;

    /* dominators (section 9.6.1): dom(entry) = {entry},
       dom(b) = {b} union the intersection of dom(p) over the predecessors p of b */
    const int W = (n + 63) / 64;
    unsigned long long *dom = malloc(sizeof(unsigned long long) * (size_t)n * (size_t)W);
    unsigned long long *tmp = malloc(sizeof(unsigned long long) * (size_t)W);
    unsigned char *has_pred = calloc((size_t)n, 1);
    if (!dom || !tmp || !has_pred) { perror("malloc"); exit(1); }
    const int entry = entry_node = entry_of(sub->sub_first, exit_node);
    for (int k = 0; k < nedges; k++) has_pred[edge_to[k]] = 1;
    for (int b = 0; b < n; b++)
        for (int w = 0; w < W; w++) dom[b * W + w] = ~0ULL;
    for (int w = 0; w < W; w++) dom[entry * W + w] = 0;
    dom[entry * W + entry / 64] |= 1ULL << (entry % 64);
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int b = 0; b < n; b++) {
            if (b == entry) continue;
            for (int w = 0; w < W; w++) tmp[w] = has_pred[b] ? ~0ULL : 0;
            for (int k = 0; k < nedges; k++)
                if (edge_to[k] == b)
                    for (int w = 0; w < W; w++) tmp[w] &= dom[edge_from[k] * W + w];
            tmp[b / 64] |= 1ULL << (b % 64);
            for (int w = 0; w < W; w++)
                if (tmp[w] != dom[b * W + w]) { dom[b * W + w] = tmp[w]; changed = 1; }
        }
    }

    /* natural loops (section 9.6.6): for each back edge t -> h, where h dominates t,
       the nodes that reach t without passing through h; loops with the same head merge */
    int *stack = malloc(sizeof(int) * (size_t)n);
    for (int e = 0; e < nedges; e++) {
        int t = edge_from[e], h = edge_to[e];
        if (!((dom[t * W + h / 64] >> (h % 64)) & 1)) continue;
        g.back_edges++;
        int r = 0;
        while (r < nregions && regions[r].head != h) r++;
        if (r == nregions) {
            if (nregions == MAX_REGIONS) continue;
            regions[r].head = h;
            regions[r].members = calloc((size_t)n, 1);
            regions[r].defs = calloc((size_t)sub->items + 1, 1);
            regions[r].members[h] = 1;
            nregions++;
        }
        unsigned char *in = regions[r].members;
        int top = 0;
        if (!in[t]) { in[t] = 1; stack[top++] = t; }
        while (top) {
            int x = stack[--top];
            for (int k = 0; k < nedges; k++)
                if (edge_to[k] == x && !in[edge_from[k]]) { in[edge_from[k]] = 1; stack[top++] = edge_from[k]; }
        }
    }
    for (int r = 0; r < nregions; r++) {
        regions[r].size = 0;
        for (int x = 0; x < n; x++) regions[r].size += regions[r].members[x];
    }

    /* Algorithm 9.52 orders the loop regions from the innermost outwards; a region's
       summary is the union of the summaries of the regions directly inside it and of
       its own statements */
    for (int a = 0; a < nregions; a++)
        for (int b = a + 1; b < nregions; b++)
            if (regions[b].size < regions[a].size) { LoopRegion t2 = regions[a]; regions[a] = regions[b]; regions[b] = t2; }
    unsigned char *covered = malloc((size_t)n);
    for (int r = 0; r < nregions; r++) {
        memset(covered, 0, (size_t)n);
        for (int q = 0; q < r; q++) {
            int inside = 1;
            for (int x = 0; x < n && inside; x++)
                if (regions[q].members[x] && !regions[r].members[x]) inside = 0;
            if (!inside) continue;
            for (int v = 0; v <= sub->items; v++) regions[r].defs[v] |= regions[q].defs[v];
            for (int x = 0; x < n; x++) covered[x] |= regions[q].members[x];
        }
        DefCtx c = {regions[r].defs};
        for (int x = 0; x < ncfg; x++)
            if (regions[r].members[x] && !covered[x] && node_expr(x)) node_defs(node_expr(x), &c);
    }
    g.loop_regions += nregions;
    free(covered);
    free(stack);
    free(has_pred);
    free(tmp);
    free(dom);
    return 1;
}

/* ======================================================================
 * 1. Region-based constant propagation with folding
 * ====================================================================== */
typedef struct { int v; long long c; } Fact;
/* Facts at a program point. `dead` marks a point that control cannot reach
 * (after a jump or return): it is the top element of the meet. */
typedef struct { Fact f[256]; int n; int dead; } Facts;

static int fact_get(const Facts *s, int v, long long *c) {
    for (int k = 0; k < s->n; k++)
        if (s->f[k].v == v) { *c = s->f[k].c; return 1; }
    return 0;
}
static void fact_kill(Facts *s, int v) {
    for (int k = 0; k < s->n; k++)
        if (s->f[k].v == v) { s->f[k] = s->f[--s->n]; return; }
}
static void fact_set(Facts *s, int v, long long c) {
    fact_kill(s, v);
    if (s->n < 256) { s->f[s->n].v = v; s->f[s->n].c = c; s->n++; }
}
static void fact_clear(Facts *s) { s->n = 0; s->dead = 0; }
static void fact_jump(Facts *s) { s->n = 0; s->dead = 1; }
static void fact_meet(Facts *a, const Facts *b) { /* a := a meet b */
    if (b->dead) return;
    if (a->dead) { *a = *b; return; }
    for (int k = 0; k < a->n;) {
        long long c;
        if (!fact_get(b, a->f[k].v, &c) || c != a->f[k].c) a->f[k] = a->f[--a->n];
        else k++;
    }
}

/* What cp_expr does with a use whose value is known: rewrite it, record it (to
 * compare analyses without changing the IR), or nothing (a transfer function). */
enum { CP_REWRITE, CP_RECORD, CP_TRANSFER };
static int cp_mode = CP_REWRITE;

typedef struct { expr_node **node; long long *val; int n, cap; } UseLog;
static UseLog *cp_log;
static void log_use(UseLog *l, expr_node *id, long long c) {
    if (l->n == l->cap) {
        l->cap = l->cap ? 2 * l->cap : 256;
        l->node = realloc(l->node, sizeof *l->node * (size_t)l->cap);
        l->val = realloc(l->val, sizeof *l->val * (size_t)l->cap);
        if (!l->node || !l->val) { perror("realloc"); exit(1); }
    }
    l->node[l->n] = id;
    l->val[l->n] = c;
    l->n++;
}

static void cp_use(expr_node *id, void *vs) {
    const Facts *s = vs;
    int v = var_of(id);
    long long c;
    if (!v || !fact_get(s, v, &c)) return;
    if (cp_mode == CP_REWRITE) {
        become_constant(id, c);
        g.constants_propagated++;
    } else if (cp_mode == CP_RECORD) {
        log_use(cp_log, id, c);
    }
}

/* Value of e under the facts s, by the rules of fold: what e folds to once the
 * known variables are replaced by their constants. */
static int const_eval(const expr_node *e, const Facts *s, long long *v) {
    if (!e) return 0;
    if (e->operator == CONSTANT) return int_const(e, v);
    if (e->operator == IDENTIFIER) return var_of(e) && fact_get(s, var_of(e), v) && in_int32(*v);
    if (has_list(e->operator) || !foldable_type(e)) return 0;
    long long a, b = 0;
    if (!const_eval(e->left, s, &a)) return 0;
    if (e->operator != NEGOP && !const_eval(e->right, s, &b)) return 0;
    return compute(e->operator, a, b, v);
}

/* Variables written inside e before the value of e is complete: everything except
 * the targets of a top-level assignment chain a = b = ... = rhs. A read sequenced
 * after such a write (x = 4, x) must not see the old fact, so these are killed
 * before uses are rewritten. */
static void inner_effects(expr_node *e, Effects *fx) {
    expr_node *a = e;
    while (a && a->operator == ASSIGN) {
        if (!var_of(a->left)) effects_of(a->left, fx);
        a = a->right;
    }
    effects_of(a, fx);
}

/* Rewrites the uses, folds, then applies the statement's effect to the facts.
 * For an assignment chain a = b = ... = e, every target gets e's value. */
static void cp_expr(expr_node *e, Facts *s) {
    if (!e) return;
    Effects in = NO_EFFECTS;
    inner_effects(e, &in);
    if (in.overflow) s->n = 0;
    for (int d = 0; d < in.n; d++) fact_kill(s, in.defs[d]);
    walk_uses(e, cp_use, s);
    if (cp_mode == CP_REWRITE) fold_tree(e);
    expr_node *last = e;
    while (last->operator == ASSIGN && last->right && last->right->operator == ASSIGN) last = last->right;
    long long c;
    int known = e->operator == ASSIGN && const_eval(last->right, s, &c);
    Effects fx = NO_EFFECTS;
    effects_of(e, &fx);
    if (fx.overflow) s->n = 0;
    for (int d = 0; d < fx.n; d++) fact_kill(s, fx.defs[d]);
    if (!known) return;
    for (expr_node *a = e;; a = a->right) {
        int v = var_of(a->left);
        if (v) fact_set(s, v, c);
        if (a == last) break;
    }
}

/* Entry to a loop region: the region's summary kills the facts of every variable
 * it may define, which gives the facts that hold at the head on every iteration
 * without iterating over the loop. The summary is the one Algorithm 9.52 computed
 * for the natural loop headed by this statement; the variables defined by the
 * statement's own subtree are added in case the loop has no back edge. */
static void kill_defs(expr_node *e, void *vs) {
    Facts *s = vs;
    Effects fx = NO_EFFECTS;
    effects_of(e, &fx);
    if (fx.overflow) s->n = 0;
    for (int d = 0; d < fx.n; d++) fact_kill(s, fx.defs[d]);
}
static void kill_instr_defs(instr_node *i, void *vs) { for_each_expr(i, kill_defs, vs); }

static void enter_loop_region(Facts *s, instr_node *loop) {
    int head = loop->type == DO_LOOP ? entry_of(loop->instruction, cfg_id(loop)) : cfg_id(loop);
    for (int r = 0; r < nregions; r++) {
        if (regions[r].head != head) continue;
        for (int k = 0; k < s->n;) {
            if (regions[r].defs[s->f[k].v]) s->f[k] = s->f[--s->n];
            else k++;
        }
    }
    instr_node *saved = loop->next;
    loop->next = NULL; /* the loop statement and its nested statements only */
    for_each_instr(loop, kill_instr_defs, s);
    loop->next = saved;
}

static void cp_seq(instr_node *i, Facts *s);

/* Exit of a loop or switch region: the facts at its entry less what the region may
 * define, unless a goto can enter it from outside. */
static void leave_region(Facts *s, const Facts *entry_less_defs, instr_node *stmt) {
    if (entered_by_goto(stmt)) fact_clear(s);
    else *s = *entry_less_defs;
}

static void cp_one(instr_node *i, Facts *s) {
    switch (i->type) {
    case EXPRESSION:
        cp_expr(i->expression, s);
        break;
    case S_RETURN:
        cp_expr(i->expression, s);
        fact_jump(s);
        break;
    case IF_BRANCH: {
        cp_expr(i->expression, s);
        Facts t = *s, e = *s;
        cp_seq(i->instruction, &t);
        cp_seq(i->tail_instruction, &e);
        fact_meet(&t, &e);
        *s = t;
        break;
    }
    case WHILE_LOOP: {
        enter_loop_region(s, i);
        cp_expr(i->expression, s);
        Facts body = *s, out = *s;
        cp_seq(i->instruction, &body);
        leave_region(s, &out, i);
        break;
    }
    case DO_LOOP: {
        enter_loop_region(s, i);
        Facts body = *s;
        cp_seq(i->instruction, &body);
        cp_expr(i->expression, s);
        Facts out = *s;
        leave_region(s, &out, i);
        break;
    }
    case FOR_LOOP: {
        expr_list *init = i->ex_list;
        if (init) cp_expr(init->expression, s);
        enter_loop_region(s, i);
        if (init && init->next) cp_expr(init->next->expression, s);
        Facts body = *s, out = *s;
        cp_seq(i->tail_instruction, &body);
        if (init && init->next && init->next->next) {
            Facts step = *s;
            cp_expr(init->next->next->expression, &step);
        }
        leave_region(s, &out, i);
        break;
    }
    case SELECT_BRANCH: {
        /* each case label joins the facts after the switch test with the facts
           falling through from the case above */
        cp_expr(i->expression, s);
        Facts head = *s, cur;
        fact_jump(&cur); /* nothing falls into the first label */
        for (instr_node *b = switch_body(i); b; b = b->next) {
            if (is_goto_target(b)) fact_clear(&cur);
            else if (is_label_of(i, b)) fact_meet(&cur, &head);
            cp_one(b, &cur);
        }
        Facts out = head;
        instr_node *saved = i->next;
        i->next = NULL;
        for_each_instr(i, kill_instr_defs, &out);
        i->next = saved;
        leave_region(s, &out, i);
        break;
    }
    default: /* goto, break, continue */
        fact_jump(s);
        break;
    }
}

static void cp_seq(instr_node *i, Facts *s) {
    for (; i; i = i->next) {
        if (is_target(i)) fact_clear(s);
        cp_one(i, s);
    }
}

/* ======================================================================
 * 1b. Iterative constant propagation (sections 9.3 and 9.4: the iterative algorithm
 *     on the control-flow graph, meet = intersection, until nothing changes)
 * ====================================================================== */
static int facts_equal(const Facts *a, const Facts *b) {
    if (a->dead != b->dead || a->n != b->n) return 0;
    for (int k = 0; k < a->n; k++) {
        long long c;
        if (!fact_get(b, a->f[k].v, &c) || c != a->f[k].c) return 0;
    }
    return 1;
}

/* the transfer function of node k */
static void transfer(int k, Facts *s) {
    expr_node *e = node_expr(k);
    if (!e || s->dead) return;
    int saved = cp_mode;
    cp_mode = CP_TRANSFER;
    cp_expr(e, s);
    cp_mode = saved;
}

#define ITERATIVE_MAX_PASSES 10000

/* Facts at the entry of every node, found iteratively; the caller frees them. */
static Facts *iterative_in(void) {
    const int n = exit_node + 1;
    Facts *in = malloc(sizeof *in * (size_t)n), *out = malloc(sizeof *out * (size_t)n);
    if (!in || !out) { perror("malloc"); exit(1); }
    for (int k = 0; k < n; k++) { fact_jump(&in[k]); fact_jump(&out[k]); } /* top: not reached yet */
    /* The meet and transfer functions are monotone, so the passes stop after at
     * most (nodes x variables) changes; the cap is a guard against a bug, and
     * giving up means knowing nothing anywhere, which is always safe. */
    int changed = 1, passes = 0;
    while (changed) {
        changed = 0;
        g.iterative_passes++;
        if (++passes > ITERATIVE_MAX_PASSES) {
            for (int k = 0; k < n; k++) fact_clear(&in[k]);
            g.iterative_gave_up++;
            break;
        }
        for (int b = 0; b < n; b++) {
            Facts m;
            if (b == entry_node) fact_clear(&m); /* nothing is known on entry */
            else fact_jump(&m);
            for (int e = 0; e < nedges; e++)
                if (edge_to[e] == b) fact_meet(&m, &out[edge_from[e]]);
            if (facts_equal(&m, &in[b])) continue;
            in[b] = m;
            out[b] = m;
            transfer(b, &out[b]);
            changed = 1;
        }
    }
    free(out);
    return in;
}

/* Rewrites (or records) every node's uses with the facts at its entry. */
static void iterative_cp(int mode) {
    Facts *in = iterative_in();
    int saved = cp_mode;
    cp_mode = mode;
    for (int k = 0; k < ncfg; k++) {
        if (!node_expr(k)) continue;
        Facts s = in[k];
        cp_expr(node_expr(k), &s);
    }
    cp_mode = saved;
    free(in);
}

/* Region-based against iterative: the uses each analysis finds constant. The
 * region-based summaries are coarser (they forget everything a loop may
 * redefine), so every use it finds must be found by the iterative analysis too,
 * with the same value. */
static void compare_analyses(void) {
    UseLog region = {0}, iter = {0};
    Facts s;
    fact_clear(&s);
    cp_mode = CP_RECORD;
    cp_log = &region;
    cp_seq(S->sub_first, &s);
    cp_log = &iter;
    iterative_cp(CP_RECORD);
    cp_mode = CP_REWRITE;
    cp_log = NULL;
    for (int a = 0; a < region.n; a++) {
        int found = 0;
        for (int b = 0; b < iter.n && !found; b++)
            if (iter.node[b] == region.node[a]) {
                found = 1;
                if (iter.val[b] != region.val[a]) g.cmp_disagree++;
            }
        if (!found) g.cmp_region_only++;
    }
    g.cmp_region += region.n;
    g.cmp_iterative += iter.n;
    free(region.node); free(region.val);
    free(iter.node); free(iter.val);
}

/* ======================================================================
 * 2-3. Copy propagation and common-subexpression elimination (straight-line)
 * ====================================================================== */
typedef struct { int dst; expr_node *src; } Copy;
typedef struct { Copy c[64]; int nc; expr_node *lhs[64]; expr_node *rhs[64]; int na; } Local;

static void local_reset(Local *L) { L->nc = L->na = 0; }

static void copy_use(expr_node *id, void *vl) {
    Local *L = vl;
    int v = var_of(id);
    for (int k = 0; v && k < L->nc; k++)
        if (L->c[k].dst == v) {
            become_identifier(id, L->c[k].src->identifier);
            g.copies_propagated++;
            return;
        }
}

static void local_kill(Local *L, int v) {
    for (int k = 0; k < L->nc;)
        if (L->c[k].dst == v || var_of(L->c[k].src) == v) L->c[k] = L->c[--L->nc];
        else k++;
    for (int k = 0; k < L->na;)
        if (var_of(L->lhs[k]) == v || expr_uses_var(L->rhs[k], v)) {
            L->lhs[k] = L->lhs[L->na - 1];
            L->rhs[k] = L->rhs[L->na - 1];
            L->na--;
        } else k++;
}

static void local_stmt(expr_node *e, Local *L) {
    if (!e) return;
    Effects in = NO_EFFECTS;
    inner_effects(e, &in);
    if (in.overflow) local_reset(L);
    for (int d = 0; d < in.n; d++) local_kill(L, in.defs[d]);
    walk_uses(e, copy_use, L);
    int v = (e->operator == ASSIGN) ? var_of(e->left) : 0;
    int candidate = v && e->right && !is_leaf(e->right->operator) && pure_expr(e->right);
    if (candidate)
        for (int k = 0; k < L->na; k++)
            if (expr_equal(L->rhs[k], e->right)) {
                become_identifier(e->right, L->lhs[k]->identifier);
                g.cse++;
                candidate = 0;
                break;
            }
    Effects fx = NO_EFFECTS;
    effects_of(e, &fx);
    if (fx.overflow) local_reset(L);
    for (int d = 0; d < fx.n; d++) local_kill(L, fx.defs[d]);
    if (candidate && !expr_uses_var(e->right, v) && L->na < 64) {
        L->lhs[L->na] = e->left;
        L->rhs[L->na] = e->right;
        L->na++;
    }
    int src = v ? var_of(e->right) : 0;
    if (src && src != v && L->nc < 64) {
        L->c[L->nc].dst = v;
        L->c[L->nc].src = e->right;
        L->nc++;
    }
}

static void local_seq(instr_node *i) {
    Local L;
    local_reset(&L);
    for (; i; i = i->next) {
        if (is_target(i)) local_reset(&L);
        switch (i->type) {
        case EXPRESSION:
            local_stmt(i->expression, &L);
            break;
        case IF_BRANCH:
            local_stmt(i->expression, &L);
            local_seq(i->instruction);
            local_seq(i->tail_instruction);
            local_reset(&L);
            break;
        case WHILE_LOOP: case DO_LOOP:
            local_reset(&L);
            local_seq(i->instruction);
            break;
        case FOR_LOOP:
            local_reset(&L);
            local_seq(i->tail_instruction);
            break;
        case SELECT_BRANCH:
            local_stmt(i->expression, &L);
            local_seq(switch_body(i));
            local_reset(&L);
            break;
        case S_RETURN:
            local_stmt(i->expression, &L);
            local_reset(&L);
            break;
        default:
            local_reset(&L);
            break;
        }
    }
}

/* ======================================================================
 * 3b. Loop-invariant code motion (section 9.5 of the book, in a safe form)
 *
 * An integer expression whose variables the loop never writes has the same
 * value on every iteration. It is computed once into a new temporary, by an
 * instruction inserted before the loop, and the loop reads the temporary:
 *
 *   while (i < n) { s = s + a * b; ... }   ->   t = a * b; while (i < n) { s = s + t; ... }
 *
 * Only expressions that cannot fail or have a side effect are moved (no
 * division, memory access or call), so computing one before a loop that runs
 * zero times changes nothing. A loop that is a jump target is left alone, since
 * the jump would skip an instruction inserted before it.
 * ====================================================================== */
static unsigned char *loop_defs;
static int loop_defs_size;

static int invariant(const expr_node *e) {
    if (!e) return 0;
    if (e->operator == CONSTANT) return int_kind(e->constant);
    if (e->operator == IDENTIFIER) {
        int v = var_of(e);
        return v && v < loop_defs_size && !loop_defs[v];
    }
    if (!(e->type & SCALAR_INT) || (e->type & NOT_SCALAR)) return 0;
    switch (e->operator) {
    case PLUSOP: case MINUSOP: case MULOP: case LSHIFT: case RSHIFT: case BITANDOP: case BITOROP: case XOROP:
        return invariant(e->left) && invariant(e->right);
    case NEGOP: case CMPLOP:
        return invariant(e->left);
    default:
        return 0;
    }
}

static int has_variable(const expr_node *e) {
    if (!e) return 0;
    if (e->operator == IDENTIFIER) return 1;
    if (e->operator == CONSTANT) return 0;
    return has_variable(e->left) || (e->operator != NEGOP && e->operator != CMPLOP && has_variable(e->right));
}

/* A new local variable of type t, set up like an existing non-parameter local of
 * that type; returns its index, or 0 when there is no such local to copy. */
static int new_local(type_t t) {
    sub_struct *sub = S;
    if (sub->items >= MAX_LOCAL_IDS - 1) return 0;
    int model = 0;
    for (int k = sub->params + 1; k < sub->items && !model; k++)
        if (sub->locals[k].type == t && !sub->locals[k].structure) model = k;
    if (!model) return 0;
    int k = sub->items++;
    sub->locals[k] = sub->locals[model];
    char *name = malloc(32);
    if (!name) { perror("malloc"); exit(1); }
    snprintf(name, 32, "licm%d", k);
    sub->locals[k].name = name;
    names_size += (int)strlen(name) + 1; /* the IR file stores every name in one table of this size */
    sub->locals[k].address_used = 0;
    unsigned char *grown = realloc(addr_taken, (size_t)sub->items + 1);
    if (!grown) { perror("realloc"); exit(1); }
    addr_taken = grown;
    addr_taken[k] = 0;
    g.temps++;
    return k;
}

/* An identifier node for local k, copied from an identifier of an existing local. */
static const id_struct *id_model;
static expr_node *local_leaf(int k, type_t t) {
    id_struct *id = malloc(sizeof *id);
    if (!id) { perror("malloc"); exit(1); }
    *id = *id_model;
    id->type = t;
    id->param = NOPARAM;
    id->rec_index = -k;
    expr_node *leaf = create_identifier_leaf(id);
    leaf->type = t;
    leaf->isbool = 0;
    leaf->ada_type_index = -1;
    return leaf;
}

typedef struct { expr_node *expr; int temp; } Hoisted;
typedef struct { instr_node *loop; instr_node **link; Hoisted h[64]; int nh; } LicmCtx;

/* Moves *slot out of the loop, or reuses the temporary of an equal expression. */
static void hoist(expr_node **slot, LicmCtx *c) {
    expr_node *e = *slot;
    for (int k = 0; k < c->nh; k++)
        if (c->h[k].expr->type == e->type && expr_equal(c->h[k].expr, e)) {
            expr_node *leaf = local_leaf(c->h[k].temp, e->type);
            become_identifier(e, leaf->identifier);
            delete_expression(leaf);
            g.hoisted++;
            return;
        }
    if (c->nh == 64) return;
    int t = new_local(e->type);
    if (!t) return;
    expr_node *use = local_leaf(t, e->type);
    use->parent = e->parent;
    use->index = e->index;
    use->instruction = e->instruction;
    *slot = use;
    expr_node *target = local_leaf(t, e->type);
    expr_node *assign = create_expr_node(ASSIGN, target, e);
    assign->type = e->type;
    assign->isbool = 0;
    assign->ada_type_index = -1;
    assign->parent = NULL;
    target->parent = assign;
    target->index = 0;
    e->parent = assign;
    e->index = 1;
    instr_node *init = create_e_instr(EXPRESSION, assign);
    init->sub = S;
    init->parent = c->loop->parent;
    set_instruction(assign, init);
    init->next = c->loop;
    *c->link = init;
    c->link = &init->next;
    c->h[c->nh].expr = e;
    c->h[c->nh].temp = t;
    c->nh++;
    g.hoisted++;
}

static void hoist_slot(expr_node **slot, int lvalue, void *vc) {
    expr_node *e = *slot;
    if (!e || is_leaf(e->operator)) return;
    if (!lvalue && invariant(e) && has_variable(e)) { hoist(slot, vc); return; }
    for_children(e, hoist_slot, vc);
}

static void hoist_instr(instr_node *i, void *vc) {
    switch (i->type) {
    case EXPRESSION: case S_RETURN: case IF_BRANCH: case WHILE_LOOP: case DO_LOOP: case SELECT_BRANCH:
        hoist_slot(&i->expression, 0, vc);
        break;
    case FOR_LOOP:
        for (expr_list *l = i->ex_list; l; l = l->next) hoist_slot(&l->expression, 0, vc);
        break;
    default:
        break;
    }
}

static void mark_loop_def(expr_node *e, void *ctx) {
    (void)ctx;
    Effects fx = NO_EFFECTS;
    effects_of(e, &fx);
    if (fx.overflow) memset(loop_defs, 1, (size_t)loop_defs_size);
    for (int d = 0; d < fx.n; d++)
        if (fx.defs[d] < loop_defs_size) loop_defs[fx.defs[d]] = 1;
}
static void mark_loop_defs(instr_node *i, void *ctx) { for_each_expr(i, mark_loop_def, ctx); }

/* *link holds the loop statement. */
static void licm_loop(instr_node **link) {
    LicmCtx c;
    c.loop = *link;
    c.link = link;
    c.nh = 0;
    loop_defs_size = S->items + 1;
    loop_defs = calloc((size_t)loop_defs_size, 1);
    if (!loop_defs) { perror("calloc"); exit(1); }
    instr_node *loop = c.loop, *saved = loop->next;
    loop->next = NULL; /* the loop statement and its nested statements only */
    for_each_instr(loop, mark_loop_defs, NULL);
    loop->next = saved;
    if (loop->type == FOR_LOOP) { /* the initialization runs once: only the test and the step */
        expr_list *l = loop->ex_list;
        if (l && l->next) hoist_slot(&l->next->expression, 0, &c);
        if (l && l->next && l->next->next) hoist_slot(&l->next->next->expression, 0, &c);
        for_each_instr(loop->tail_instruction, hoist_instr, &c);
    } else {
        hoist_slot(&loop->expression, 0, &c);
        for_each_instr(loop->instruction, hoist_instr, &c);
    }
    free(loop_defs);
    loop_defs = NULL;
}

/* Walks a statement list through its links, outer loops before inner ones. */
static void licm_list(instr_node **link) {
    for (; *link; link = &(*link)->next) {
        instr_node *i = *link;
        int is_loop = i->type == WHILE_LOOP || i->type == DO_LOOP || i->type == FOR_LOOP;
        if (is_loop && !is_target(i)) {
            licm_loop(link);
            while (*link != i) link = &(*link)->next; /* past the inserted instructions */
        }
        switch (i->type) {
        case IF_BRANCH: licm_list(&i->instruction); licm_list(&i->tail_instruction); break;
        case WHILE_LOOP: case DO_LOOP: licm_list(&i->instruction); break;
        case FOR_LOOP: licm_list(&i->tail_instruction); break;
        case SELECT_BRANCH: {
            instr_node *body = switch_body(i); /* starts at a case label: nothing goes before it */
            licm_list(&body);
            break;
        }
        default: break;
        }
    }
}

/* the identifier of a non-parameter local, as the model for new identifiers */
static void find_id_model(expr_node *id, void *ctx) {
    (void)ctx;
    if (!id_model && var_of(id) && id->identifier->param == NOPARAM) id_model = id->identifier;
}
static void find_id_model_expr(expr_node *e, void *ctx) { walk_uses(e, find_id_model, ctx); }
static void find_id_model_instr(instr_node *i, void *ctx) { for_each_expr(i, find_id_model_expr, ctx); }

static void loop_invariant_code_motion(sub_struct *sub) {
    id_model = NULL;
    for_each_instr(sub->sub_first, find_id_model_instr, NULL);
    if (id_model) licm_list(&sub->sub_first);
}

/* ======================================================================
 * 4. Dead-code elimination
 * ====================================================================== */
static unsigned char *read_var;

static void mark_read(expr_node *id, void *ctx) {
    (void)ctx;
    int v = var_of(id);
    if (v) read_var[v] = 1;
}

/* Marks reads anywhere in e, including the targets of x += ... and x++. */
static void mark_expr(expr_node *e, void *ctx);
static void mark_slot(expr_node **slot, int lvalue, void *ctx) {
    (void)lvalue;
    mark_expr(*slot, ctx);
}
static void mark_expr(expr_node *e, void *ctx) {
    if (!e) return;
    if (is_ident(e)) return; /* handled by walk_uses below */
    if ((is_incdec(e->operator) || (is_assign_op(e->operator) && e->operator != ASSIGN)) && var_of(e->left))
        read_var[var_of(e->left)] = 1;
    for_children(e, mark_slot, ctx);
}
static void mark_instr_expr(expr_node *e, void *ctx) {
    walk_uses(e, mark_read, NULL);
    mark_expr(e, ctx);
}
static void mark_instr(instr_node *i, void *ctx) { for_each_expr(i, mark_instr_expr, ctx); }

typedef struct { int removed; } DceCtx;
static void dce_instr(instr_node *i, void *vc) {
    DceCtx *c = vc;
    if (i->type != EXPRESSION || !i->expression) return;
    expr_node *e = i->expression;
    int v = (e->operator == ASSIGN) ? var_of(e->left) : 0;
    if (!v || read_var[v] || side_effects(e->right)) return;
    delete_expression(e);
    i->expression = NULL;
    c->removed++;
}

static void dead_code_elimination(sub_struct *sub) {
    read_var = calloc((size_t)sub->items + 1, 1);
    DceCtx c;
    do {
        c.removed = 0;
        memset(read_var, 0, (size_t)sub->items + 1);
        for_each_instr(sub->sub_first, mark_instr, NULL);
        for_each_instr(sub->sub_first, dce_instr, &c);
        g.dead_removed += c.removed;
    } while (c.removed);
    free(read_var);
}

/* ======================================================================
 * Driver
 * ====================================================================== */
static void count_loops(instr_node *i, void *ctx) {
    (void)ctx;
    if (i->type == WHILE_LOOP || i->type == DO_LOOP || i->type == FOR_LOOP) g.loop_statements++;
}

/* Marks every local whose address is taken: the operand of & after any
 * indexing or field selection, e.g. &x, &a[i], &s.f. */
static void mark_address(expr_node *e) {
    while (e && (e->operator == ARRAY || e->operator == FIELD)) e = e->left;
    if (is_ident(e) && !(e->identifier->type & TYPE_FUNCTION) && e->identifier->rec_index < 0) {
        int k = -e->identifier->rec_index;
        if (k < S->items) addr_taken[k] = 1;
    }
}
static void find_address_slot(expr_node **slot, int lvalue, void *ctx);
static void find_address_expr(expr_node *e, void *ctx) {
    if (!e || is_leaf(e->operator)) return;
    if (e->operator == ADDRESSOF) mark_address(e->left);
    for_children(e, find_address_slot, ctx);
}
static void find_address_slot(expr_node **slot, int lvalue, void *ctx) {
    (void)lvalue;
    find_address_expr(*slot, ctx);
}
static void find_address_instr(instr_node *i, void *ctx) { for_each_expr(i, find_address_expr, ctx); }

/* Which analysis rewrites the program: the region-based one (default) or the
 * iterative one (option -iterative). Both always run and are compared. */
int my_opt_iterative = 0;

static void optimize_subroutine(sub_struct *sub) {
    S = sub;
    free(addr_taken);
    addr_taken = calloc((size_t)sub->items + 1, 1);
    if (!addr_taken) { perror("calloc"); exit(1); }
    for_each_instr(sub->sub_first, find_address_instr, NULL);
    ngotos = nlabels = targets_overflow = 0;
    for_each_instr(sub->sub_first, collect_target, NULL);
    if (!analyse_cfg(sub)) { /* too large for the tables: left as it is */
        g.skipped++;
        free(addr_taken);
        addr_taken = NULL;
        return;
    }
    for_each_instr(sub->sub_first, count_loops, NULL);

    compare_analyses();
    if (my_opt_iterative) {
        iterative_cp(CP_REWRITE);
    } else {
        Facts s;
        fact_clear(&s);
        cp_seq(sub->sub_first, &s);
    }
    loop_invariant_code_motion(sub);
    local_seq(sub->sub_first);
    dead_code_elimination(sub);
    free(addr_taken);
    addr_taken = NULL;
}

void my_optimization(void) {
    memset(&g, 0, sizeof g);
    for (int i = 0; i < subroutine_number; i++) {
        sub_struct *sub = subroutines[i];
        if (!sub || sub->library || !sub->sub_first) continue;
        optimize_subroutine(sub);
    }
    free_regions();
    if (!my_opt_verbose) return;
    printf("[REPORT] instructions %d, CFG edges %d, back edges %d (loop statements %d), loop regions %d, "
           "functions skipped %d\n",
           g.instructions, g.cfg_edges, g.back_edges, g.loop_statements, g.loop_regions, g.skipped);
    printf("[REPORT] constant uses found: region-based %d, iterative %d (%d passes); "
           "region-based uses the iterative analysis missed %d, values that differ %d, gave up %d\n",
           g.cmp_region, g.cmp_iterative, g.iterative_passes, g.cmp_region_only, g.cmp_disagree,
           g.iterative_gave_up);
    printf("[REPORT] %s constant propagation: constants propagated %d, expressions folded %d, simplified %d\n",
           my_opt_iterative ? "iterative" : "region-based", g.constants_propagated, g.folded, g.simplified);
    printf("[REPORT] loop-invariant expressions moved %d (into %d new temporaries), copies propagated %d, "
           "common subexpressions %d, dead assignments removed %d\n",
           g.hoisted, g.temps, g.copies_propagated, g.cse, g.dead_removed);
}

#ifndef MY_OPT_NO_MAIN
int main(int argc, char *argv[]) {
    if (argc < 2) {
        printf("No input IR file provided!\n");
        exit(1);
    }
    if (argc > 2 && strcmp(argv[2], "-iterative") == 0) my_opt_iterative = 1;
    if (load_intermediate(argv[1])) {
        printf("Unable to read input IR file!\n");
        exit(1);
    }
    my_optimization();
    if (store_intermediate("result.ir")) {
        printf("Unable to write output IR file!\n");
        exit(1);
    }
    return 0;
}
#endif

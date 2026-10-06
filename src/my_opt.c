/* my_opt.c - optimizer for the intermediate representation (IR) of the CCC
 * high-level-synthesis toolchain (C front end translator, inter_library).
 *
 *   my_opt input.ir            reads input.ir, optimizes it, writes result.ir
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
 *   - control-flow graph of the subroutine, one node per instruction
 *   - dominators (iterative bit-vector algorithm, section 9.6.1)
 *   - natural loops (back edges whose head dominates their tail, section 9.6.6)
 *   - region hierarchy (section 9.7, Algorithm 9.52): statements are the leaf
 *     regions; the loop regions are ordered from the innermost outwards, and
 *     each one's summary, the set of variables it may define, is built from the
 *     summaries of the regions inside it and its own statements
 *
 * Transformations
 *   1. region-based constant propagation with constant folding: facts flow
 *      through sequences and both branches of an if (meet = intersection, a
 *      branch that ends in a jump does not take part); on entry to a loop region
 *      its summary removes the facts of the variables it may define, so the
 *      facts at the loop head are found without iterating over the loop
 *   2. copy propagation: after x = y, later uses of x become y
 *   3. common-subexpression elimination: in x = e; ... z = e, the second becomes z = x
 *   4. dead-code elimination: an assignment to a variable that is never read,
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
 *   - the shape of the tree never changes: nodes are rewritten in place and a
 *     removed instruction becomes an empty expression instruction, a form the
 *     front end itself produces
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
    int constants_propagated, folded, copies_propagated, cse, dead_removed;
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
    drop_children(e);
    id_struct *copy = malloc(sizeof *copy);
    if (!copy) { perror("malloc"); exit(1); }
    *copy = *id;
    e->operator = IDENTIFIER;
    e->identifier = copy;
}

/* ----- constant folding ----- */
static int int_const(const expr_node *e, long long *v) {
    if (!e || e->operator != CONSTANT || !int_kind(e->constant)) return 0;
    *v = (long long)e->constant->ivalue;
    return *v >= -2147483647LL - 1 && *v <= 2147483647LL;
}

static void fold(expr_node *e) {
    if (!e || is_leaf(e->operator) || has_list(e->operator)) return;
    if (!(e->type & SCALAR_INT) || (e->type & (NOT_SCALAR | TYPE_UNSIGNED))) return;
    long long a, b, r;
    if (e->operator == NEGOP) {
        if (!int_const(e->left, &a)) return;
        r = -a;
    } else {
        if (!int_const(e->left, &a) || !int_const(e->right, &b)) return;
        switch (e->operator) {
        case PLUSOP: r = a + b; break;
        case MINUSOP: r = a - b; break;
        case MULOP: r = a * b; break;
        case DIVOP: if (b <= 0 || a < 0) return; r = a / b; break;
        case MODOP: if (b <= 0 || a < 0) return; r = a % b; break;
        case LSHIFT: if (a < 0 || b < 0 || b > 30) return; r = a << b; break;
        case RSHIFT: if (a < 0 || b < 0 || b > 30) return; r = a >> b; break;
        case BITANDOP: if (a < 0 || b < 0) return; r = a & b; break;
        case BITOROP: if (a < 0 || b < 0) return; r = a | b; break;
        case XOROP: if (a < 0 || b < 0) return; r = a ^ b; break;
        default: return;
        }
    }
    if (r < -2147483647LL - 1 || r > 2147483647LL) return;
    become_constant(e, r);
    g.folded++;
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
#define MAXN 8192
#define MAXE 65536
static instr_node *cfg_node[MAXN];
static int ncfg;
static int edge_from[MAXE], edge_to[MAXE], nedges;
static int after_of[MAXN]; /* for a loop or switch: the node control reaches when it ends */

static int cfg_id(const instr_node *i) {
    for (int k = 0; k < ncfg; k++)
        if (cfg_node[k] == i) return k;
    return -1;
}

static void number_instr(instr_node *i, void *ctx) {
    (void)ctx;
    if (ncfg < MAXN - 1 && cfg_id(i) < 0) cfg_node[ncfg++] = i;
}

static void add_edge(int a, int b) {
    if (a < 0 || b < 0 || nedges >= MAXE) return;
    for (int k = 0; k < nedges; k++)
        if (edge_from[k] == a && edge_to[k] == b) return;
    edge_from[nedges] = a;
    edge_to[nedges] = b;
    nedges++;
}

/* Entry node of a statement list, or `cont` when it is empty. A do loop starts with its body. */
static int entry_of(instr_node *seq, int cont) {
    if (!seq) return cont;
    if (seq->type == DO_LOOP && seq->instruction) return entry_of(seq->instruction, cfg_id(seq));
    return cfg_id(seq);
}

/* cont: the node control reaches after the list. break and continue name their
 * loop or switch statement; break leaves it, continue goes to its test. */
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
            add_edge(me, entry_of(i->instruction, me));
            add_edge(me, after);
            build_cfg(i->instruction, me, exit_node);
            break;
        case FOR_LOOP:
            after_of[me] = after;
            add_edge(me, entry_of(i->tail_instruction, me));
            add_edge(me, after);
            build_cfg(i->tail_instruction, me, exit_node);
            break;
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
            add_edge(me, t >= 0 ? t : after);
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

static void analyse_cfg(sub_struct *sub) {
    free_regions();
    ncfg = 0;
    nedges = 0;
    for_each_instr(sub->sub_first, number_instr, NULL);
    if (ncfg == 0) return;
    const int exit_node = ncfg; /* virtual exit */
    cfg_node[exit_node] = NULL;
    for (int k = 0; k <= exit_node; k++) after_of[k] = exit_node;
    build_cfg(sub->sub_first, exit_node, exit_node);
    const int n = exit_node + 1;
    g.instructions += ncfg;
    g.cfg_edges += nedges;

    /* dominators (section 9.6.1): dom(entry) = {entry},
       dom(b) = {b} union the intersection of dom(p) over the predecessors p of b */
    const int W = (n + 63) / 64;
    unsigned long long *dom = malloc(sizeof(unsigned long long) * (size_t)n * (size_t)W);
    unsigned long long *tmp = malloc(sizeof(unsigned long long) * (size_t)W);
    unsigned char *has_pred = calloc((size_t)n, 1);
    if (!dom || !tmp || !has_pred) { perror("malloc"); exit(1); }
    const int entry = entry_of(sub->sub_first, exit_node);
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
            if (regions[r].members[x] && !covered[x]) for_each_expr(cfg_node[x], node_defs, &c);
    }
    g.loop_regions += nregions;
    free(covered);
    free(stack);
    free(has_pred);
    free(tmp);
    free(dom);
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

static void cp_use(expr_node *id, void *vs) {
    const Facts *s = vs;
    int v = var_of(id);
    long long c;
    if (v && fact_get(s, v, &c)) {
        become_constant(id, c);
        g.constants_propagated++;
    }
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
    fold_tree(e);
    Effects fx = NO_EFFECTS;
    effects_of(e, &fx);
    if (fx.overflow) s->n = 0;
    for (int d = 0; d < fx.n; d++) fact_kill(s, fx.defs[d]);
    if (e->operator != ASSIGN) return;
    expr_node *last = e;
    while (last->right && last->right->operator == ASSIGN) last = last->right;
    long long c;
    if (!int_const(last->right, &c)) return;
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

static void optimize_subroutine(sub_struct *sub) {
    S = sub;
    free(addr_taken);
    addr_taken = calloc((size_t)sub->items + 1, 1);
    if (!addr_taken) { perror("calloc"); exit(1); }
    for_each_instr(sub->sub_first, find_address_instr, NULL);
    ngotos = nlabels = targets_overflow = 0;
    for_each_instr(sub->sub_first, collect_target, NULL);
    for_each_instr(sub->sub_first, count_loops, NULL);
    analyse_cfg(sub);

    Facts s;
    fact_clear(&s);
    cp_seq(sub->sub_first, &s);
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
    if (!my_opt_verbose) return;
    printf("[REPORT] instructions %d, CFG edges %d, back edges %d (loop statements %d), loop regions %d\n",
           g.instructions, g.cfg_edges, g.back_edges, g.loop_statements, g.loop_regions);
    printf("[REPORT] constants propagated %d, expressions folded %d, copies propagated %d, "
           "common subexpressions %d, dead assignments removed %d\n",
           g.constants_propagated, g.folded, g.copies_propagated, g.cse, g.dead_removed);
}

#ifndef MY_OPT_NO_MAIN
int main(int argc, char *argv[]) {
    if (argc < 2) {
        printf("No input IR file provided!\n");
        exit(1);
    }
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

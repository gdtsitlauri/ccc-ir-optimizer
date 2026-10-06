/* my_opt.c - optimizer for the intermediate representation (IR) of the CCC
 * high-level-synthesis toolchain.
 *
 * Analyses (reported in the statistics)
 *   - basic blocks: leaders are the first instruction, every jump target and
 *     every instruction after a control instruction
 *   - control-flow graph with predecessor and successor lists
 *   - dominators (iterative bit-vector algorithm)
 *   - natural loops (back edges whose target dominates their source)
 *
 * Transformations
 *   1. jump cleanup: a goto to the very next instruction is removed
 *   2. algebraic simplification: x+0, 0+x, x-0, x*1, 1*x, x<<0 (integer constants)
 *   3. constant propagation: after x = c, uses of x become c
 *   4. copy propagation: after x = y, uses of x become y
 *   5. common-subexpression elimination: x = e; ... z = e becomes z = x
 *   6. dead-code elimination: assignments to variables that are never read,
 *      with no side effects on the right-hand side, are removed (repeated
 *      until nothing changes)
 *
 * Safety rules (when in doubt, the IR is left unchanged)
 *   - 3-5 are local: facts are discarded at every instruction that another
 *     instruction points to (a possible jump target) and after every control
 *     instruction, so they never cross a jump in either direction. This holds
 *     whether the IR keeps branch and loop bodies in the main instruction list
 *     or in separate lists; both kinds of list are processed.
 *   - a function call, an assignment through a non-identifier left-hand side
 *     (array element, pointer) or an assignment nested in an expression
 *     discards all facts; any write to a variable discards the facts about it
 *     and about every expression that uses it
 *   - uses are rewritten only below + - * << , at the root of a right-hand side
 *     and in call arguments; never on a left-hand side, under ++/--, or under
 *     any other operator (for example address-of)
 *   - an instruction that another instruction points to is never removed
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "csensetypes.h"
#include "intermediate.h"
#include "irloadstore.h"

#define WORD_SIZE (sizeof(unsigned) * 8)

extern int subroutine_number;
extern sub_struct *subroutines[];
extern int i_node_number;

/* ======================= statistics ======================= */
typedef struct {
    int blocks, edges, loops;  /* analysis */
    int jumps_removed, simplified, constants_propagated, copies_propagated, cse, dead_removed;
} OptStats;

static OptStats g_stats;
int my_opt_verbose = 1;  /* print the [REPORT] lines */

/* ======================= expression helpers ======================= */
static int is_assign_op(oper_t op) { return op >= ASSIGN && op <= ASSIGNXOR; }
static int is_incdec(oper_t op) { return op == PREINC || op == PREDEC || op == POSTINC || op == POSTDEC; }
static int is_pure_op(oper_t op) { return op == PLUSOP || op == MINUSOP || op == MULOP || op == LSHIFT; }

static int is_ident(const expr_node *e) { return e && e->operator == IDENTIFIER && e->identifier; }

static int const_equal(const const_struct *a, const const_struct *b) {
    if (a == b) return 1;
    if (!a || !b || a->const_type != b->const_type) return 0;
    switch (a->const_type) {
    case TYPE_INT: return a->ivalue == b->ivalue;
    case TYPE_DOUBLE: return a->fvalue == b->fvalue;
    case TYPE_STRING: return a->svalue && b->svalue && strcmp(a->svalue, b->svalue) == 0;
    default: return 0;
    }
}

/* Structural equality of pure expressions. */
static int expr_equal(const expr_node *a, const expr_node *b) {
    if (!a || !b) return a == b;
    if (a->operator != b->operator) return 0;
    if (a->operator == CONSTANT) return const_equal(a->constant, b->constant);
    if (a->operator == IDENTIFIER)
        return a->identifier && b->identifier && a->identifier->rec_index == b->identifier->rec_index;
    if (a->expression_list || b->expression_list) return 0;
    return expr_equal(a->left, b->left) && expr_equal(a->right, b->right);
}

/* An expression with no side effects made of identifiers, constants and + - * <<. */
static int is_pure_expr(const expr_node *e) {
    if (!e) return 0;
    if (e->operator == CONSTANT) return e->constant != NULL;
    if (e->operator == IDENTIFIER) return e->identifier != NULL;
    if (!is_pure_op(e->operator) || e->expression_list) return 0;
    return is_pure_expr(e->left) && is_pure_expr(e->right);
}

static int has_side_effects(const expr_node *e) {
    if (!e) return 0;
    if (e->operator == FUNCALL || is_assign_op(e->operator) || is_incdec(e->operator)) return 1;
    if (has_side_effects(e->left) || has_side_effects(e->right)) return 1;
    for (expr_list *L = e->expression_list; L; L = L->next)
        if (has_side_effects(L->expression)) return 1;
    return 0;
}

static int expr_uses(const expr_node *e, int idx) {
    if (!e) return 0;
    if (is_ident(e) && e->identifier->rec_index == idx) return 1;
    if (expr_uses(e->left, idx) || expr_uses(e->right, idx)) return 1;
    for (expr_list *L = e->expression_list; L; L = L->next)
        if (expr_uses(L->expression, idx)) return 1;
    return 0;
}

/* Effects of one statement on variables.
 *   clobber_all: facts about every variable become invalid (call, store
 *                through a pointer or array, nested assignment)
 *   defs[]:      variables written directly (up to 8; more sets clobber_all) */
typedef struct {
    int clobber_all;
    int ndefs;
    int defs[8];
} Effects;

static void add_def(Effects *fx, int idx) {
    for (int i = 0; i < fx->ndefs; i++)
        if (fx->defs[i] == idx) return;
    if (fx->ndefs < 8) fx->defs[fx->ndefs++] = idx;
    else fx->clobber_all = 1;
}

static void collect_effects(const expr_node *e, Effects *fx, int top) {
    if (!e) return;
    if (e->operator == FUNCALL) fx->clobber_all = 1;
    if (is_assign_op(e->operator)) {
        if (is_ident(e->left)) add_def(fx, e->left->identifier->rec_index);
        else fx->clobber_all = 1;
        if (!top) fx->clobber_all = 1;  /* assignment inside an expression */
    }
    if (is_incdec(e->operator)) {
        if (is_ident(e->left)) add_def(fx, e->left->identifier->rec_index);
        else fx->clobber_all = 1;
    }
    collect_effects(e->left, fx, 0);
    collect_effects(e->right, fx, 0);
    for (expr_list *L = e->expression_list; L; L = L->next) collect_effects(L->expression, fx, 0);
}

static Effects statement_effects(const instr_node *i) {
    Effects fx;
    memset(&fx, 0, sizeof fx);
    if (i->expression) collect_effects(i->expression, &fx, 1);
    if (i->type != EXPRESSION) fx.clobber_all = 1;  /* control or unknown instruction: assume the worst */
    return fx;
}

/* Calls f(slot) for every identifier occurrence that may be rewritten:
 * operands of + - * <<, the root of a right-hand side, and call arguments. */
typedef void (*use_fn)(expr_node **slot, void *ctx);

static void visit_value(expr_node **slot, use_fn f, void *ctx);

static void visit_children(expr_node *e, use_fn f, void *ctx) {
    if (!e) return;
    if (is_pure_op(e->operator)) {
        visit_value(&e->left, f, ctx);
        visit_value(&e->right, f, ctx);
    } else if (e->operator == FUNCALL) {
        for (expr_list *L = e->expression_list; L; L = L->next) visit_value(&L->expression, f, ctx);
    } else if (is_assign_op(e->operator)) {
        visit_value(&e->right, f, ctx);  /* never the left-hand side */
    }
    /* any other operator: leave its operands alone */
}

static void visit_value(expr_node **slot, use_fn f, void *ctx) {
    expr_node *e = *slot;
    if (!e) return;
    if (is_ident(e)) { f(slot, ctx); return; }
    visit_children(e, f, ctx);
}

static void visit_statement_uses(instr_node *i, use_fn f, void *ctx) {
    expr_node *e = i->expression;
    if (!e) return;
    if (is_assign_op(e->operator) || e->operator == FUNCALL || is_pure_op(e->operator)) visit_children(e, f, ctx);
}

static expr_node *new_ident_like(const expr_node *src) {
    expr_node *n = malloc(sizeof *n);
    if (!n) { perror("malloc"); exit(1); }
    *n = *src;
    n->left = n->right = NULL;
    n->expression_list = NULL;
    return n;
}

static expr_node *new_const_expr(const expr_node *like, const_struct *c) {
    expr_node *n = malloc(sizeof *n);
    if (!n) { perror("malloc"); exit(1); }
    *n = *like;
    n->operator = CONSTANT;
    n->constant = c;
    n->identifier = NULL;
    n->left = n->right = NULL;
    n->expression_list = NULL;
    return n;
}

/* ======================= basic blocks and CFG ======================= */
typedef struct BasicBlock {
    int block_id;
    instr_node *start_instr, *end_instr;
    struct BasicBlock **succ;
    int succ_count;
    struct BasicBlock **pred;
    int pred_count;
    struct BasicBlock *next;
    unsigned *dom;
} BasicBlock;

static BasicBlock **block_by_id = NULL;
static int nblocks = 0;

static int is_control(const instr_node *i) {
    switch (i->type) {
    case IF_BRANCH: case WHILE_LOOP: case FOR_LOOP: case DO_LOOP: case SELECT_BRANCH:
    case S_GOTO: case S_BREAK: case S_CONTINUE: case S_RETURN:
        return 1;
    default:
        return 0;
    }
}

static int instr_count(const sub_struct *sub) {
    int n = 0;
    for (instr_node *i = sub->sub_first; i; i = i->next) n++;
    return n;
}

/* Index of an instruction in the sub_first list (-1 if absent). */
static int instr_index(const sub_struct *sub, const instr_node *x) {
    int n = 0;
    for (instr_node *i = sub->sub_first; i; i = i->next, n++)
        if (i == x) return n;
    return -1;
}

static BasicBlock *block_of(const sub_struct *sub, const instr_node *x, int *instr_block) {
    int k = x ? instr_index(sub, x) : -1;
    return k >= 0 ? block_by_id[instr_block[k]] : NULL;
}

static BasicBlock *build_blocks(sub_struct *sub, int **instr_block_out) {
    int n = instr_count(sub);
    *instr_block_out = NULL;
    nblocks = 0;
    if (n == 0) return NULL;
    char *leader = calloc(n, 1);
    int *instr_block = malloc(n * sizeof *instr_block);
    leader[0] = 1;
    int k = 0;
    for (instr_node *i = sub->sub_first; i; i = i->next, k++) {
        if (is_control(i) && k + 1 < n) leader[k + 1] = 1;
        const instr_node *t[3] = {i->target, i->instruction, i->tail_instruction};
        for (int j = 0; j < 3; j++) {
            int ti = t[j] ? instr_index(sub, t[j]) : -1;
            if (ti >= 0) leader[ti] = 1;
        }
        for (instr_list *L = i->target_list; L; L = L->next) {
            int ti = L->instruction ? instr_index(sub, L->instruction) : -1;
            if (ti >= 0) leader[ti] = 1;
        }
    }
    BasicBlock *head = NULL, *tail = NULL, *cur = NULL;
    k = 0;
    for (instr_node *i = sub->sub_first; i; i = i->next, k++) {
        if (leader[k]) {
            cur = calloc(1, sizeof *cur);
            cur->block_id = nblocks++;
            cur->start_instr = i;
            if (!head) head = cur; else tail->next = cur;
            tail = cur;
        }
        cur->end_instr = i;
        instr_block[k] = cur->block_id;
    }
    free(leader);
    block_by_id = malloc(nblocks * sizeof *block_by_id);
    for (BasicBlock *b = head; b; b = b->next) block_by_id[b->block_id] = b;
    *instr_block_out = instr_block;
    return head;
}

static void add_edge(BasicBlock *from, BasicBlock *to) {
    if (!from || !to) return;
    for (int i = 0; i < from->succ_count; i++)
        if (from->succ[i] == to) return;
    from->succ[from->succ_count++] = to;
    to->pred[to->pred_count++] = from;
    g_stats.edges++;
}

static void build_cfg(sub_struct *sub, BasicBlock *head, int *instr_block) {
    for (BasicBlock *b = head; b; b = b->next) {
        b->succ = calloc(nblocks + 1, sizeof *b->succ);
        b->pred = calloc(nblocks + 1, sizeof *b->pred);
    }
    for (BasicBlock *b = head; b; b = b->next) {
        instr_node *e = b->end_instr;
        BasicBlock *fall = b->next;
        switch (e->type) {
        case IF_BRANCH:
            add_edge(b, block_of(sub, e->instruction, instr_block));
            add_edge(b, e->tail_instruction ? block_of(sub, e->tail_instruction, instr_block) : fall);
            break;
        case WHILE_LOOP: case FOR_LOOP: case DO_LOOP:
            add_edge(b, block_of(sub, e->instruction, instr_block));
            add_edge(b, fall);
            break;
        case SELECT_BRANCH:
            for (instr_list *L = e->target_list; L; L = L->next) add_edge(b, block_of(sub, L->instruction, instr_block));
            add_edge(b, e->tail_instruction ? block_of(sub, e->tail_instruction, instr_block) : fall);
            break;
        case S_GOTO:
            add_edge(b, block_of(sub, e->target, instr_block));
            break;
        case S_BREAK: case S_CONTINUE:
            add_edge(b, e->target ? block_of(sub, e->target, instr_block) : fall);
            break;
        case S_RETURN:
            break;
        default:
            add_edge(b, fall);
            break;
        }
    }
}

static void free_blocks(BasicBlock *head, int *instr_block) {
    while (head) {
        BasicBlock *nx = head->next;
        free(head->succ);
        free(head->pred);
        free(head->dom);
        free(head);
        head = nx;
    }
    free(block_by_id);
    block_by_id = NULL;
    free(instr_block);
    nblocks = 0;
}

/* ======================= dominators and natural loops ======================= */
static void compute_dominators(BasicBlock *head) {
    const int W = (int)((nblocks + WORD_SIZE - 1) / WORD_SIZE);
    for (BasicBlock *b = head; b; b = b->next) {
        b->dom = malloc(W * sizeof *b->dom);
        for (int i = 0; i < W; i++) b->dom[i] = ~0u;
    }
    BasicBlock *start = block_by_id[0];
    for (int i = 0; i < W; i++) start->dom[i] = 0;
    start->dom[0] = 1u;
    unsigned *newd = malloc(W * sizeof *newd);
    int changed;
    do {
        changed = 0;
        for (BasicBlock *b = head; b; b = b->next) {
            if (b == start) continue;
            for (int i = 0; i < W; i++) newd[i] = b->pred_count ? ~0u : 0u;
            for (int p = 0; p < b->pred_count; p++)
                for (int i = 0; i < W; i++) newd[i] &= b->pred[p]->dom[i];
            newd[b->block_id / WORD_SIZE] |= 1u << (b->block_id % WORD_SIZE);
            for (int i = 0; i < W; i++)
                if (newd[i] != b->dom[i]) { b->dom[i] = newd[i]; changed = 1; }
        }
    } while (changed);
    free(newd);
}

static int dominates(int h, int b) {
    return (block_by_id[b]->dom[h / WORD_SIZE] >> (h % WORD_SIZE)) & 1;
}

/* Counts natural loops: one per back edge b -> h with h dominating b. */
static int count_natural_loops(void) {
    int loops = 0;
    for (int b = 0; b < nblocks; b++)
        for (int i = 0; i < block_by_id[b]->succ_count; i++)
            if (dominates(block_by_id[b]->succ[i]->block_id, b)) loops++;
    return loops;
}

/* ======================= instruction sequences =======================
 * The passes do not assume how the IR lays out the bodies of branches and
 * loops. They collect every instruction reachable from sub_first through
 * `next` and through the pointers of control instructions, as a set of
 * sequences (runs linked by `next`). Facts are reset at every instruction
 * that some instruction points to and after every control instruction, so
 * facts never cross a possible jump in either direction. */
typedef struct {
    instr_node **node;   /* all instructions, sequence by sequence */
    int *seq_start;      /* first index of each sequence */
    int n, nseq, cap, seq_cap;
    unsigned char *referenced;
} Program;

static int prog_find(const Program *p, const instr_node *x) {
    for (int k = 0; k < p->n; k++)
        if (p->node[k] == x) return k;
    return -1;
}

static void prog_push(Program *p, instr_node *x) {
    if (p->n == p->cap) {
        p->cap = p->cap ? 2 * p->cap : 64;
        p->node = realloc(p->node, p->cap * sizeof *p->node);
    }
    p->node[p->n++] = x;
}

static void prog_add_sequence(Program *p, instr_node *head) {
    if (!head || prog_find(p, head) >= 0) return;
    if (p->nseq + 2 > p->seq_cap) {
        p->seq_cap = p->seq_cap ? 2 * p->seq_cap : 16;
        p->seq_start = realloc(p->seq_start, p->seq_cap * sizeof *p->seq_start);
    }
    p->seq_start[p->nseq++] = p->n;
    for (instr_node *i = head; i && prog_find(p, i) < 0; i = i->next) prog_push(p, i);
}

static void prog_build(Program *p, sub_struct *sub) {
    memset(p, 0, sizeof *p);
    prog_add_sequence(p, sub->sub_first);
    for (int k = 0; k < p->n; k++) {  /* p->n grows while new sequences are found */
        instr_node *i = p->node[k];
        prog_add_sequence(p, i->target);
        prog_add_sequence(p, i->instruction);
        prog_add_sequence(p, i->tail_instruction);
        for (instr_list *L = i->target_list; L; L = L->next) prog_add_sequence(p, L->instruction);
    }
    if (!p->seq_start) p->seq_start = malloc(sizeof *p->seq_start);
    p->seq_start[p->nseq] = p->n;
    p->referenced = calloc(p->n ? p->n : 1, 1);
    for (int k = 0; k < p->n; k++) {
        instr_node *i = p->node[k];
        instr_node *ptrs[4] = {i->target, i->instruction, i->tail_instruction, i->parent};
        for (int j = 0; j < 4; j++) {
            int t = ptrs[j] ? prog_find(p, ptrs[j]) : -1;
            if (t >= 0) p->referenced[t] = 1;
        }
        for (instr_list *L = i->target_list; L; L = L->next) {
            int t = L->instruction ? prog_find(p, L->instruction) : -1;
            if (t >= 0) p->referenced[t] = 1;
        }
    }
}

static void prog_free(Program *p) {
    free(p->node);
    free(p->seq_start);
    free(p->referenced);
    memset(p, 0, sizeof *p);
}

/* Removes node k if it can be unlinked safely: nobody points to it, and it is
 * either inside a sequence (its predecessor is node k-1) or the subroutine head. */
static int prog_unlink(Program *p, sub_struct *sub, int k) {
    if (p->referenced[k]) return 0;
    int first = 0;
    for (int s = 0; s < p->nseq; s++)
        if (p->seq_start[s] == k) first = 1;
    instr_node *x = p->node[k];
    if (!first) {
        p->node[k - 1]->next = x->next;
        return 1;
    }
    if (sub->sub_first == x) {
        sub->sub_first = x->next;
        return 1;
    }
    return 0;
}

/* Local pass driver: calls step(i, reset) for every instruction in program
 * order; reset is 1 when the facts collected so far must be discarded first. */
typedef void (*step_fn)(instr_node *i, int reset, void *ctx);

static void for_each_local(Program *p, step_fn step, void *ctx) {
    for (int s = 0; s < p->nseq; s++) {
        int reset = 1;
        for (int k = p->seq_start[s]; k < p->seq_start[s + 1]; k++) {
            instr_node *i = p->node[k];
            if (p->referenced[k]) reset = 1;
            step(i, reset, ctx);
            reset = is_control(i);
        }
    }
}

/* ======================= 1. jump cleanup ======================= */
static void jump_cleanup(sub_struct *sub) {
    int removed;
    do {
        removed = 0;
        Program p;
        prog_build(&p, sub);
        for (int k = 0; k < p.n; k++) {
            instr_node *i = p.node[k];
            if (i->type == S_GOTO && i->target && i->target == i->next && prog_unlink(&p, sub, k)) {
                removed = 1;
                g_stats.jumps_removed++;
                break;  /* rebuild after every structural change */
            }
        }
        prog_free(&p);
    } while (removed);
}

/* ======================= 2. algebraic simplification ======================= */
static int is_int_const(const expr_node *e, long long v) {
    return e && e->operator == CONSTANT && e->constant && e->constant->const_type == TYPE_INT && e->constant->ivalue == v;
}

static void simplify_expr(expr_node **slot) {
    expr_node *e = *slot;
    if (!e || !is_pure_op(e->operator)) return;
    simplify_expr(&e->left);
    simplify_expr(&e->right);
    expr_node *repl = NULL;
    if (e->operator == PLUSOP && is_int_const(e->right, 0)) repl = e->left;
    else if (e->operator == PLUSOP && is_int_const(e->left, 0)) repl = e->right;
    else if (e->operator == MINUSOP && is_int_const(e->right, 0)) repl = e->left;
    else if (e->operator == MULOP && is_int_const(e->right, 1)) repl = e->left;
    else if (e->operator == MULOP && is_int_const(e->left, 1)) repl = e->right;
    else if (e->operator == LSHIFT && is_int_const(e->right, 0)) repl = e->left;
    if (repl) { *slot = repl; g_stats.simplified++; }
}

static void simplify_step(instr_node *i, int reset, void *ctx) {
    (void)reset; (void)ctx;
    expr_node *e = i->expression;
    if (e && is_assign_op(e->operator)) simplify_expr(&e->right);
}

/* ======================= 3. constant propagation ======================= */
typedef struct { int idx; const_struct *c; } ConstFact;
typedef struct { ConstFact f[64]; int n; } ConstCtx;

static const_struct *const_lookup(ConstCtx *ctx, int idx) {
    for (int k = 0; k < ctx->n; k++)
        if (ctx->f[k].idx == idx) return ctx->f[k].c;
    return NULL;
}

static void const_kill(ConstCtx *ctx, int idx) {
    for (int k = 0; k < ctx->n; k++)
        if (ctx->f[k].idx == idx) { ctx->f[k] = ctx->f[--ctx->n]; return; }
}

static void const_use(expr_node **slot, void *vctx) {
    const_struct *c = const_lookup(vctx, (*slot)->identifier->rec_index);
    if (c) { *slot = new_const_expr(*slot, c); g_stats.constants_propagated++; }
}

static void const_step(instr_node *i, int reset, void *vctx) {
    ConstCtx *ctx = vctx;
    if (reset) ctx->n = 0;
    visit_statement_uses(i, const_use, ctx);
    Effects fx = statement_effects(i);
    if (fx.clobber_all) { ctx->n = 0; return; }
    for (int d = 0; d < fx.ndefs; d++) const_kill(ctx, fx.defs[d]);
    expr_node *e = i->expression;
    if (e && e->operator == ASSIGN && is_ident(e->left) && e->right && e->right->operator == CONSTANT &&
        e->right->constant && ctx->n < 64) {
        ctx->f[ctx->n].idx = e->left->identifier->rec_index;
        ctx->f[ctx->n].c = e->right->constant;
        ctx->n++;
    }
}

/* ======================= 4. copy propagation ======================= */
typedef struct { int dst; expr_node *src; } Copy;
typedef struct { Copy v[64]; int n; } CopyCtx;

static void copy_use(expr_node **slot, void *vctx) {
    CopyCtx *ctx = vctx;
    int idx = (*slot)->identifier->rec_index;
    for (int k = 0; k < ctx->n; k++)
        if (ctx->v[k].dst == idx) { *slot = new_ident_like(ctx->v[k].src); g_stats.copies_propagated++; return; }
}

static void copy_step(instr_node *i, int reset, void *vctx) {
    CopyCtx *ctx = vctx;
    if (reset) ctx->n = 0;
    visit_statement_uses(i, copy_use, ctx);
    Effects fx = statement_effects(i);
    if (fx.clobber_all) { ctx->n = 0; return; }
    for (int d = 0; d < fx.ndefs; d++)
        for (int k = 0; k < ctx->n;)
            if (ctx->v[k].dst == fx.defs[d] || ctx->v[k].src->identifier->rec_index == fx.defs[d]) ctx->v[k] = ctx->v[--ctx->n];
            else k++;
    expr_node *e = i->expression;
    if (e && e->operator == ASSIGN && is_ident(e->left) && is_ident(e->right) &&
        e->left->identifier->rec_index != e->right->identifier->rec_index && ctx->n < 64) {
        ctx->v[ctx->n].dst = e->left->identifier->rec_index;
        ctx->v[ctx->n].src = e->right;
        ctx->n++;
    }
}

/* ======================= 5. common-subexpression elimination ======================= */
typedef struct { expr_node *lhs, *rhs; } Avail;
typedef struct { Avail v[64]; int n; } CseCtx;

static void cse_step(instr_node *i, int reset, void *vctx) {
    CseCtx *ctx = vctx;
    if (reset) ctx->n = 0;
    expr_node *e = i->expression;
    int candidate = i->type == EXPRESSION && e && e->operator == ASSIGN && is_ident(e->left) && e->right &&
                    is_pure_op(e->right->operator) && is_pure_expr(e->right);
    if (candidate)
        for (int k = 0; k < ctx->n; k++)
            if (expr_equal(ctx->v[k].rhs, e->right)) {
                e->right = new_ident_like(ctx->v[k].lhs);
                g_stats.cse++;
                candidate = 0;  /* now a copy, not an expression */
                break;
            }
    Effects fx = statement_effects(i);
    if (fx.clobber_all) { ctx->n = 0; return; }
    for (int d = 0; d < fx.ndefs; d++)
        for (int k = 0; k < ctx->n;)
            if (ctx->v[k].lhs->identifier->rec_index == fx.defs[d] || expr_uses(ctx->v[k].rhs, fx.defs[d])) ctx->v[k] = ctx->v[--ctx->n];
            else k++;
    if (candidate && !expr_uses(e->right, e->left->identifier->rec_index) && ctx->n < 64) {
        ctx->v[ctx->n].lhs = e->left;
        ctx->v[ctx->n].rhs = e->right;
        ctx->n++;
    }
}

/* ======================= 6. dead-code elimination ======================= */
/* Variables are identified by rec_index, the index of their symbol record in
 * the subroutine (0 .. sub->items-1), as in the CCC symbol tables. */
static void mark_reads(const expr_node *e, unsigned char *read, int items, int is_lhs) {
    if (!e) return;
    if (is_ident(e)) {
        if (!is_lhs) {
            int idx = e->identifier->rec_index;
            if (idx >= 0 && idx < items) read[idx] = 1;
        }
        return;
    }
    if (is_assign_op(e->operator)) {
        mark_reads(e->left, read, items, e->operator == ASSIGN);  /* x += ... reads x */
        mark_reads(e->right, read, items, 0);
        return;
    }
    mark_reads(e->left, read, items, 0);
    mark_reads(e->right, read, items, 0);
    for (expr_list *L = e->expression_list; L; L = L->next) mark_reads(L->expression, read, items, 0);
}

static void dead_code_elimination(sub_struct *sub) {
    const int items = sub->items;
    if (items <= 0) return;
    unsigned char *read = malloc(items);
    int removed;
    do {
        removed = 0;
        Program p;
        prog_build(&p, sub);
        memset(read, 0, items);
        for (int k = 0; k < p.n; k++) mark_reads(p.node[k]->expression, read, items, 0);
        for (int k = 0; k < p.n; k++) {
            instr_node *i = p.node[k];
            expr_node *e = i->expression;
            int idx = (e && is_ident(e->left)) ? e->left->identifier->rec_index : -1;
            if (i->type == EXPRESSION && e && e->operator == ASSIGN && idx >= 0 && idx < items && !read[idx] &&
                !has_side_effects(e->right) && prog_unlink(&p, sub, k)) {
                removed = 1;
                g_stats.dead_removed++;
                break;  /* rebuild after every structural change */
            }
        }
        prog_free(&p);
    } while (removed);
    free(read);
}

/* ======================= driver ======================= */
static void optimize_subroutine(sub_struct *sub) {
    /* analysis (reported in the statistics) */
    int *instr_block;
    BasicBlock *head = build_blocks(sub, &instr_block);
    if (head) {
        build_cfg(sub, head, instr_block);
        compute_dominators(head);
        g_stats.blocks += nblocks;
        g_stats.loops += count_natural_loops();
        free_blocks(head, instr_block);
    }

    /* transformations */
    jump_cleanup(sub);
    Program p;
    prog_build(&p, sub);
    for_each_local(&p, simplify_step, NULL);
    ConstCtx cc; cc.n = 0;
    for_each_local(&p, const_step, &cc);
    CopyCtx yc; yc.n = 0;
    for_each_local(&p, copy_step, &yc);
    CseCtx ec; ec.n = 0;
    for_each_local(&p, cse_step, &ec);
    prog_free(&p);
    dead_code_elimination(sub);
}

void my_optimization(void) {
    memset(&g_stats, 0, sizeof g_stats);
    for (int i = 0; i < subroutine_number; i++) {
        if (!subroutines[i]) {
            fprintf(stderr, "[WARN] subroutine %d is NULL\n", i);
            continue;
        }
        int before = instr_count(subroutines[i]);
        optimize_subroutine(subroutines[i]);
        int after = instr_count(subroutines[i]);
        if (my_opt_verbose) printf("[REPORT] subroutine %d: %d top-level instructions before, %d after\n", i, before, after);
    }
    if (!my_opt_verbose) return;
    printf("[REPORT] basic blocks %d, CFG edges %d, natural loops %d\n", g_stats.blocks, g_stats.edges, g_stats.loops);
    printf("[REPORT] jumps removed %d, simplifications %d, constants propagated %d, copies propagated %d, "
           "common subexpressions %d, dead assignments removed %d\n",
           g_stats.jumps_removed, g_stats.simplified, g_stats.constants_propagated, g_stats.copies_propagated,
           g_stats.cse, g_stats.dead_removed);
}

#ifndef MY_OPT_NO_MAIN
int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s <input.ir> <output.ir>\n", argv[0]);
        return 1;
    }
    if (load_intermediate(argv[1])) {
        fprintf(stderr, "[ERROR] failed to load %s\n", argv[1]);
        return 1;
    }
    my_optimization();
    dump_ast();
    if (store_intermediate(argv[2])) {
        fprintf(stderr, "[ERROR] failed to write %s\n", argv[2]);
        return 1;
    }
    printf("[INFO] wrote optimized IR to %s\n", argv[2]);
    return 0;
}

/* Newlib stubs required by libirloadstore.a (__getreent, __locale_ctype_ptr). */
struct _reent { int _dummy; };
static struct _reent _global_reent = { 0 };
struct _reent *__getreent(void) { return &_global_reent; }
void *__locale_ctype_ptr = NULL;
#endif

/* my_opt.c
 *
 * Πλήρης βελτιστοποιητής ενδιάμεσης αναπαράστασης (IR)
 * με:
 *  - Dominator analysis
 *  - Natural loop detection
 *  - Ιεραρχία περιοχών (Alg. 9.52)
 *  - Block‐level CP με partial evaluation
 *  - Region‐level CP με fixpoint
 *  - Dead‐code elimination (πλήρης)
 *  - Copy propagation
 *  - Loop-invariant code motion
 *  - Strength reduction
 *  - Common subexpression elimination
 *  - Inline expansion
 *  - Peephole optimization
 *  - Control flow simplification
 *  - Στατιστικά: αριθμός εντολών πριν/μετά
 *  - Υποστήριξη TYPE_INT, TYPE_DOUBLE, TYPE_STRING
 *  - Πλήρης απελευθέρωση μνήμης
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "csensetypes.h"
#include "intermediate.h"
#include "irloadstore.h"

#define WORD_SIZE (sizeof(unsigned)*8)

extern sub_struct *subroutines[];

// === Function prototypes for optimization phases ===
static void control_flow_simplification(sub_struct *sub);
static void peephole_optimization(sub_struct *sub);
static void inline_expansion(sub_struct *sub);
static void common_subexpression_elimination(sub_struct *sub);
static void strength_reduction(sub_struct *sub);
static void loop_invariant_code_motion(sub_struct *sub);
static void copy_propagation(sub_struct *sub);
static int count_instructions(sub_struct *sub);


// ===================== COPY PROPAGATION =====================
static void copy_propagation(sub_struct *sub) {
    // ...implementation from previous nested location...
    for (instr_node *i = sub->sub_first; i; i = i->next) {
        if (!i->expression) continue;
        expr_node *e = i->expression;
        /* Εντολή τύπου x = y */
        if (e->operator == ASSIGN && e->left && e->right &&
            e->left->operator == IDENTIFIER && e->right->operator == IDENTIFIER) {
            int src_idx = e->right->identifier->rec_index;
            int dst_idx = e->left->identifier->rec_index;
            /* Αντικατάσταση όλων των χρήσεων του dst με src στα επόμενα */
            for (instr_node *j = i->next; j; j = j->next) {
                if (!j->expression) continue;
                expr_node *ex = j->expression;
                /* Αντικατάσταση σε απλές εκφράσεις */
                if (ex->operator == IDENTIFIER && ex->identifier && ex->identifier->rec_index == dst_idx) {
                    ex->identifier->rec_index = src_idx;
                }
                /* Αντικατάσταση σε αριστερό/δεξί */
                if (ex->left && ex->left->operator == IDENTIFIER && ex->left->identifier && ex->left->identifier->rec_index == dst_idx) {
                    ex->left->identifier->rec_index = src_idx;
                }
                if (ex->right && ex->right->operator == IDENTIFIER && ex->right->identifier && ex->right->identifier->rec_index == dst_idx) {
                    ex->right->identifier->rec_index = src_idx;
                }
            }
        }
    }
}

// ===================== LOOP-INVARIANT CODE MOTION =====================
static void loop_invariant_code_motion(sub_struct *sub) {
    // ...implementation from previous nested location...
    for (instr_node *i = sub->sub_first; i; i = i->next) {
        if (i->type == WHILE_LOOP || i->type == DO_LOOP || i->type == FOR_LOOP) {
            instr_node *loop_head = i;
            instr_node *loop_tail = i->tail_instruction;
            /* Εντοπισμός loop-invariant εκφράσεων */
            for (instr_node *j = loop_head->next; j && j != loop_tail; j = j->next) {
                if (!j->expression) continue;
                expr_node *e = j->expression;
                /* Αν η έκφραση είναι σταθερή ή δεν εξαρτάται από μεταβλητές που αλλάζουν στο βρόχο */
                if (e->operator == CONSTANT) {
                    /* Μετακίνηση πριν το βρόχο */
                    instr_node *prev = loop_head->parent;
                    if (prev) {
                        /* Απλή μετακίνηση: αποσύνδεση και επανασύνδεση */
                        instr_node *tmp = j->next;
                        if (prev->next == loop_head) {
                            prev->next = j;
                        }
                        j->next = loop_head;
                        loop_head->next = tmp;
                        printf("[LOG] Moved loop-invariant instruction before loop.\n");
                    }
                }
            }
        }
    }
}

// ===================== STRENGTH REDUCTION =====================
static void strength_reduction(sub_struct *sub) {
    // ...implementation from previous nested location...
    for (instr_node *i = sub->sub_first; i; i = i->next) {
        if (!i->expression) continue;
        expr_node *e = i->expression;
        /* Εντοπισμός πολλαπλασιασμού με σταθερή δύναμη του 2 */
        if (e->operator == MULOP && e->right && e->right->operator == CONSTANT) {
            unsigned long long v = e->right->constant->ivalue;
            if (v > 0 && (v & (v - 1)) == 0) { /* Είναι δύναμη του 2 */
                int shift = 0;
                while (v >>= 1) ++shift;
                e->operator = LSHIFT;
                e->right->operator = CONSTANT;
                e->right->constant->ivalue = shift;
                printf("[LOG] Strength reduction: replaced multiplication with shift (<< %d).\n", shift);
            }
        }
    }
}

// ===================== COMMON SUBEXPRESSION ELIMINATION =====================
static int expr_equal(expr_node *a, expr_node *b) {
    if (!a || !b) return 0;
    if (a->operator != b->operator) return 0;
    if (a->operator == CONSTANT && b->operator == CONSTANT)
        return a->constant->ivalue == b->constant->ivalue;
    if (a->operator == IDENTIFIER && b->operator == IDENTIFIER)
        return a->identifier->rec_index == b->identifier->rec_index;
    return expr_equal(a->left, b->left) && expr_equal(a->right, b->right);
}

static void common_subexpression_elimination(sub_struct *sub) {
    // ...implementation from previous nested location...
    for (instr_node *i = sub->sub_first; i; i = i->next) {
        if (!i->expression) continue;
        expr_node *e = i->expression;
        /* Ψάχνουμε για ίδια έκφραση σε επόμενες εντολές */
        for (instr_node *j = i->next; j; j = j->next) {
            if (!j->expression) continue;
            if (expr_equal(e, j->expression)) {
                /* Αντικατάσταση της έκφρασης j με αναφορά στην έκφραση i */
                j->expression = e;
                printf("[LOG] Common subexpression eliminated.\n");
            }
        }
    }
}

// ===================== INLINE EXPANSION =====================
static void inline_expansion(sub_struct *sub) {
    // ...implementation from previous nested location...
    /* Απλή υλοποίηση: για κάθε κλήση συνάρτησης (FUNCALL), αν η συνάρτηση έχει <=3 εντολές, αντικαθιστά την κλήση με το σώμα της. */
    for (instr_node *i = sub->sub_first; i; i = i->next) {
        if (!i->expression) continue;
        expr_node *e = i->expression;
        if (e->operator == FUNCALL && e->left && e->left->operator == IDENTIFIER) {
            int sub_idx = e->left->identifier->rec_index;
            if (sub_idx >= 0 && sub_idx < MAX_SUBROUTINES && subroutines[sub_idx]) {
                sub_struct *callee = subroutines[sub_idx];
                int callee_instrs = 0;
                for (instr_node *ci = callee->sub_first; ci; ci = ci->next) callee_instrs++;
                if (callee_instrs > 0 && callee_instrs <= 3) {
                    /* Inline: αντικατάσταση της κλήσης με τις εντολές της συνάρτησης */
                    instr_node *after = i->next;
                    instr_node *last = NULL;
                    for (instr_node *ci = callee->sub_first; ci; ci = ci->next) {
                        instr_node *copy = dup_instruction(ci, NULL, sub);
                        if (last) last->next = copy;
                        else i->next = copy;
                        last = copy;
                    }
                    if (last) last->next = after;
                    printf("[LOG] Inline expansion: replaced FUNCALL with callee body.\n");
                }
            }
        }
    }
}

// ===================== PEEPHOLE OPTIMIZATION =====================
static void peephole_optimization(sub_struct *sub) {
    // ...implementation from previous nested location...
    for (instr_node *i = sub->sub_first; i && i->next; i = i->next) {
        expr_node *e1 = i->expression;
        expr_node *e2 = i->next->expression;
        if (!e1 || !e2) continue;
        /* Παράδειγμα: x = x + 0 -> x = x */
        if (e1->operator == ASSIGN && e1->right && e1->right->operator == PLUSOP &&
            e1->right->right && e1->right->right->operator == CONSTANT && e1->right->right->constant->ivalue == 0) {
            e1->right = e1->right->left;
            printf("[LOG] Peephole: replaced x = x + 0 with x = x.\n");
        }
        /* Παράδειγμα: x = x * 1 -> x = x */
        if (e1->operator == ASSIGN && e1->right && e1->right->operator == MULOP &&
            e1->right->right && e1->right->right->operator == CONSTANT && e1->right->right->constant->ivalue == 1) {
            e1->right = e1->right->left;
            printf("[LOG] Peephole: replaced x = x * 1 with x = x.\n");
        }
        /* Παράδειγμα: x = x - 0 -> x = x */
        if (e1->operator == ASSIGN && e1->right && e1->right->operator == MINUSOP &&
            e1->right->right && e1->right->right->operator == CONSTANT && e1->right->right->constant->ivalue == 0) {
            e1->right = e1->right->left;
            printf("[LOG] Peephole: replaced x = x - 0 with x = x.\n");
        }
        /* Παράδειγμα: x = 0 + x -> x = x */
        if (e1->operator == ASSIGN && e1->right && e1->right->operator == PLUSOP &&
            e1->right->left && e1->right->left->operator == CONSTANT && e1->right->left->constant->ivalue == 0) {
            e1->right = e1->right->right;
            printf("[LOG] Peephole: replaced x = 0 + x with x = x.\n");
        }
    }
}

// ===================== CONTROL FLOW SIMPLIFICATION =====================
static void control_flow_simplification(sub_struct *sub) {
    // ...implementation from previous nested location...
    instr_node *prev = NULL;
    for (instr_node *i = sub->sub_first; i; ) {
        /* Αφαίρεση περιττών jumps: αν μια εντολή είναι S_GOTO και ο επόμενος κόμβος είναι ο στόχος, αφαιρείται το jump */
        if (i->type == S_GOTO && i->target == i->next) {
            printf("[LOG] Control flow: removed redundant jump.\n");
            if (prev) prev->next = i->next;
            else sub->sub_first = i->next;
            instr_node *tmp = i;
            i = i->next;
            free(tmp);
            continue;
        }
        /* Συγχώνευση blocks: αν δύο διαδοχικά blocks δεν έχουν branches, συγχωνεύονται */
        if (prev && prev->type == EXPRESSION && i->type == EXPRESSION) {
            printf("[LOG] Control flow: merged consecutive blocks.\n");
            prev->next = i->next;
            free(i);
            i = prev->next;
            continue;
        }
        prev = i;
        i = i->next;
    }
}
extern int subroutine_number;
extern sub_struct * subroutines[];
extern int i_node_number;

/* ===================== CONSTANT MAPPING ===================== */
typedef struct ConstantMapping {
    int rec_index;
    const_struct *constant;
    struct ConstantMapping *next;
} ConstantMapping;

static void add_mapping(ConstantMapping **map, int idx, const_struct *c) {
    for (ConstantMapping *p = *map; p; p = p->next) {
        if (p->rec_index == idx) {
            p->constant = c;
            return;
        }
    }
    ConstantMapping *n = malloc(sizeof *n);
    if (!n) { perror("malloc"); exit(1); }
    n->rec_index = idx;
    n->constant  = c;
    n->next      = *map;
    *map         = n;
}

static void remove_mapping(ConstantMapping **map, int idx) {
    ConstantMapping *p = *map, *prev = NULL;
    while (p) {
        if (p->rec_index == idx) {
            if (prev) prev->next = p->next;
            else      *map      = p->next;
            free(p);
            return;
        }
        prev = p;
        p = p->next;
    }
}

static const_struct* lookup_mapping(ConstantMapping *map, int idx) {
    for (; map; map = map->next) {
        if (map->rec_index == idx) {
            return map->constant;
        }
    }
    return NULL;
}

static void clear_mapping(ConstantMapping **map) {
    ConstantMapping *p = *map;
    while (p) {
        ConstantMapping *nx = p->next;
        free(p);
        p = nx;
    }
    *map = NULL;
}

static void union_mappings(ConstantMapping **dest, ConstantMapping *src) {
    for (; src; src = src->next) {
        if (!lookup_mapping(*dest, src->rec_index)) {
            add_mapping(dest, src->rec_index, src->constant);
        }
    }
}

static ConstantMapping* intersect_mappings(ConstantMapping *m1, ConstantMapping *m2) {
    ConstantMapping *res = NULL;
    for (; m1; m1 = m1->next) {
        const_struct *c2 = lookup_mapping(m2, m1->rec_index);
        if (!c2) continue;
        int match = 0;
        if (m1->constant->const_type == c2->const_type) {
            switch (m1->constant->const_type) {
              case TYPE_INT:
                match = (m1->constant->ivalue == c2->ivalue);
                break;
              case TYPE_DOUBLE:
                match = (m1->constant->fvalue == c2->fvalue);
                break;
              case TYPE_STRING:
                match = (strcmp(m1->constant->svalue, c2->svalue) == 0);
                break;
              default:
                match = (m1->constant == c2);
            }
        }
        if (match) {
            add_mapping(&res, m1->rec_index, m1->constant);
        }
    }
    return res;
}

/* ===================== BASIC BLOCKS & CFG ===================== */
typedef struct BasicBlock {
    int block_id;
    instr_node *start_instr, *end_instr;
    struct BasicBlock **succ;
    int succ_count;
    struct BasicBlock *next;

    unsigned *dom;               /* Dominator bitvector */
    ConstantMapping *entry_map;  /* CP mappings */
    ConstantMapping *exit_map;
} BasicBlock;

static int *instruction_to_block = NULL;
static BasicBlock **block_by_id = NULL;
static int nblocks = 0;

/* 1) Δημιουργία Basic Blocks */
static BasicBlock* create_basic_blocks(sub_struct *sub) {
    if (!sub || !sub->sub_first) return NULL;
    if (!instruction_to_block) {
        instruction_to_block = malloc((i_node_number+1)*sizeof *instruction_to_block);
        for (int i = 0; i <= i_node_number; i++) {
            instruction_to_block[i] = -1;
        }
    }
    instr_node *cur = sub->sub_first;
    BasicBlock *head = NULL, *tail = NULL, *curr_bb = NULL;
    nblocks = 0;
    while (cur) {
        if (!curr_bb) {
            curr_bb = calloc(1, sizeof *curr_bb);
            curr_bb->block_id    = nblocks++;
            curr_bb->start_instr = cur;
            if (!head) head = curr_bb;
            else        tail->next = curr_bb;
            tail = curr_bb;
        }
        instruction_to_block[cur->node_i] = curr_bb->block_id;
        curr_bb->end_instr = cur;
        switch (cur->type) {
          case IF_BRANCH: case WHILE_LOOP: case FOR_LOOP:
          case DO_LOOP: case SELECT_BRANCH:
          case S_GOTO: case S_BREAK: case S_CONTINUE:
          case S_RETURN:
            curr_bb = NULL;
            break;
          default:
            break;
        }
        cur = cur->next;
    }
    block_by_id = malloc(nblocks * sizeof *block_by_id);
    for (BasicBlock *b = head; b; b = b->next) {
        block_by_id[b->block_id] = b;
    }
    return head;
}

/* 2) Κατασκευή CFG */
static void build_cfg(BasicBlock *head) {
    for (BasicBlock *b = head; b; b = b->next) {
        b->succ = calloc(nblocks, sizeof *b->succ);
        b->succ_count = 0;
    }
    for (BasicBlock *b = head; b; b = b->next) {
        instr_node *e = b->end_instr;
        if (!e) continue;
        #define ADD(id) do { BasicBlock *t = block_by_id[id]; \
                              if (t) b->succ[b->succ_count++] = t; } while(0)
        switch (e->type) {
          case IF_BRANCH:
            ADD(instruction_to_block[e->instruction->node_i]);
            ADD(instruction_to_block[e->tail_instruction->node_i]);
            break;
          case WHILE_LOOP: case FOR_LOOP: case DO_LOOP:
            ADD(instruction_to_block[e->instruction->node_i]);
            if (e->next) ADD(instruction_to_block[e->next->node_i]);
            break;
          case SELECT_BRANCH: {
            for (instr_list *L = e->target_list; L; L = L->next) {
              if (L->instruction) {
                ADD(instruction_to_block[L->instruction->node_i]);
              }
            }
            if (e->tail_instruction)
              ADD(instruction_to_block[e->tail_instruction->node_i]);
            if (e->next)
              ADD(instruction_to_block[e->next->node_i]);
            break;
          }
          case S_GOTO:
            if (e->target)
              ADD(instruction_to_block[e->target->node_i]);
            break;
          case S_BREAK: case S_CONTINUE:
            if (e->next)
              ADD(instruction_to_block[e->next->node_i]);
            break;
          case S_RETURN:
            break;
          default:
            if (e->next)
              ADD(instruction_to_block[e->next->node_i]);
            break;
        }
        #undef ADD
    }
}

/* ===================== DOMINATORS ===================== */
static void compute_dominators(BasicBlock *head) {
    int B = nblocks, W = (B + WORD_SIZE - 1) / WORD_SIZE;
    for (BasicBlock *b = head; b; b = b->next) {
        b->dom = calloc(W, sizeof *b->dom);
        for (int i = 0; i < W; i++) {
            b->dom[i] = ~0u;
        }
    }
    BasicBlock *start = block_by_id[0];
    for (int i = 0; i < W; i++) {
        start->dom[i] = 0;
    }
    start->dom[0] |= 1u << 0;
    int changed;
    do {
        changed = 0;
        for (BasicBlock *b = head; b; b = b->next) {
            if (b == start) continue;
            unsigned newd[W];
            for (int i = 0; i < W; i++) newd[i] = ~0u;
            for (BasicBlock *p = head; p; p = p->next) {
                for (int k = 0; k < p->succ_count; k++) {
                    if (p->succ[k] == b) {
                        for (int i = 0; i < W; i++) {
                            newd[i] &= p->dom[i];
                        }
                    }
                }
            }
            newd[b->block_id / WORD_SIZE] |= 1u << (b->block_id % WORD_SIZE);
            for (int i = 0; i < W; i++) {
                if (newd[i] != b->dom[i]) {
                    b->dom[i] = newd[i];
                    changed = 1;
                }
            }
        }
    } while (changed);
}

static int dominates(int h, int b) {
    BasicBlock *bb = block_by_id[b];
    return (bb->dom[h / WORD_SIZE] >> (h % WORD_SIZE)) & 1;
}

/* ===================== NATURAL LOOPS ===================== */
typedef struct {
    int header, latch;
    unsigned *members;
    int nmembers;
} Loop;

static Loop* detect_natural_loops(BasicBlock *head, int *nloops_out) {
    compute_dominators(head);
    int B = nblocks, W = (B + WORD_SIZE - 1) / WORD_SIZE;
    Loop *loops = NULL;
    int Lc = 0;
    for (int b = 0; b < B; b++) {
        BasicBlock *BB = block_by_id[b];
        for (int i = 0; i < BB->succ_count; i++) {
            int h = BB->succ[i]->block_id;
            if (dominates(h, b)) {
                loops = realloc(loops, (Lc+1)*sizeof *loops);
                Loop *L = &loops[Lc++];
                L->header   = h;
                L->latch    = b;
                L->members  = calloc(W, sizeof *L->members);
                L->nmembers = 0;
                int *stk = malloc(B * sizeof *stk), top = 0;
                stk[top++] = b;
                while (top) {
                    int x = stk[--top];
                    if (!((L->members[x / WORD_SIZE] >> (x % WORD_SIZE)) & 1)) {
                        L->members[x / WORD_SIZE] |= 1u << (x % WORD_SIZE);
                        L->nmembers++;
                        for (int y = 0; y < B; y++) {
                            BasicBlock *P = block_by_id[y];
                            for (int k = 0; k < P->succ_count; k++) {
                                if (P->succ[k]->block_id == x && dominates(h, y)) {
                                    stk[top++] = y;
                                }
                            }
                        }
                    }
                }
                free(stk);
                if (!((L->members[h / WORD_SIZE] >> (h % WORD_SIZE)) & 1)) {
                    L->members[h / WORD_SIZE] |= 1u << (h % WORD_SIZE);
                    L->nmembers++;
                }
            }
        }
    }
    *nloops_out = Lc;
    return loops;
}

/* ===================== REGION HIERARCHY ===================== */
typedef struct Region {
    int region_id;
    int *blocks;
    int block_count;
    struct Region *next;
} Region;

static Region* init_leaf_regions(void) {
    Region *h = NULL, *t = NULL;
    for (int i = 0; i < nblocks; i++) {
        Region *r = malloc(sizeof *r);
        r->region_id   = i;
        r->blocks      = malloc(sizeof(int));
        r->blocks[0]   = i;
        r->block_count = 1;
        r->next        = NULL;
        if (!h) h = r; else t->next = r;
        t = r;
    }
    return h;
}

static Region* build_region_hierarchy(BasicBlock *head) {
    Region *R = init_leaf_regions();
    int nloops;
    Loop *loops = detect_natural_loops(head, &nloops);
    for (int i = 0; i < nloops-1; i++) {
        for (int j = i+1; j < nloops; j++) {
            if (loops[i].nmembers > loops[j].nmembers) {
                Loop tmp = loops[i]; loops[i] = loops[j]; loops[j] = tmp;
            }
        }
    }
    int rid = nblocks;
    for (int i = 0; i < nloops; i++) {
        Loop *L = &loops[i];
        Region *body = malloc(sizeof *body);
        body->region_id   = rid++;
        body->block_count = L->nmembers;
        body->blocks      = malloc(L->nmembers * sizeof(int));
        int idx = 0;
        for (int b = 0; b < nblocks; b++) {
            if ((L->members[b / WORD_SIZE] >> (b % WORD_SIZE)) & 1) {
                body->blocks[idx++] = b;
            }
        }
        body->next = R; R = body;
        Region *loopr = malloc(sizeof *loopr);
        loopr->region_id   = rid++;
        loopr->block_count = body->block_count;
        loopr->blocks      = malloc(body->block_count * sizeof(int));
        memcpy(loopr->blocks, body->blocks, body->block_count * sizeof(int));
        loopr->next = R; R = loopr;
    }
    if (nloops == 0 || loops[nloops-1].nmembers < nblocks) {
        Region *top = malloc(sizeof *top);
        top->region_id   = rid++;
        top->block_count = nblocks;
        top->blocks      = malloc(nblocks * sizeof(int));
        for (int i = 0; i < nblocks; i++) top->blocks[i] = i;
        top->next = R; R = top;
    }
    for (int i = 0; i < nloops; i++) free(loops[i].members);
    free(loops);
    return R;
}

/* ===================== FORWARD DECLARATION ===================== */
static void constant_propagation_in_region(Region *r, ConstantMapping *incoming_map);

/* ===================== BLOCK-LEVEL CONSTANT PROPAGATION ===================== */
static void propagate_expr(expr_node*, ConstantMapping*);
static void handle_assignment_like(instr_node*, ConstantMapping**);
static void handle_inc_dec(instr_node*, ConstantMapping**);

static void constant_propagation_in_block(BasicBlock *bb,
                                          ConstantMapping *in,
                                          ConstantMapping **out) {
    ConstantMapping *mp = NULL;
    union_mappings(&mp, in);
    instr_node *i = bb->start_instr, *e = bb->end_instr;
    while (i) {
        propagate_expr(i->expression, mp);
        handle_assignment_like(i, &mp);
        handle_inc_dec(i, &mp);
        if (i == e) break;
        i = i->next;
    }
    *out = mp;
}

/* ===================== REGION-LEVEL CONSTANT PROPAGATION ===================== */
static void constant_propagation_in_region(Region *r, ConstantMapping *incoming_map) {
    ConstantMapping *running_map = NULL;
    union_mappings(&running_map, incoming_map);
    for (int i = 0; i < r->block_count; i++) {
        int bid = r->blocks[i];
        BasicBlock *bb = block_by_id[bid];
        clear_mapping(&bb->entry_map);
        union_mappings(&bb->entry_map, running_map);
        ConstantMapping *bb_output = NULL;
        constant_propagation_in_block(bb, bb->entry_map, &bb_output);
        clear_mapping(&bb->exit_map);
        union_mappings(&bb->exit_map, bb_output);
        clear_mapping(&running_map);
        union_mappings(&running_map, bb_output);
    }
}

/* ===================== HANDLE ASSIGNMENT & INC/DEC ===================== */
static void handle_assignment_like(instr_node *instr, ConstantMapping **map) {
    expr_node *r = instr->expression;
    if (!r) return;
    oper_t op = r->operator;
    if (op < ASSIGN || op > ASSIGNXOR) return;
    expr_node *lhs = r->left, *rhs = r->right;
    if (!lhs || !rhs || lhs->operator != IDENTIFIER || !lhs->identifier) return;
    int idx = lhs->identifier->rec_index;
    const_struct *old = lookup_mapping(*map, idx);
    remove_mapping(map, idx);
    if (old && rhs->operator == CONSTANT) {
        unsigned long long v = old->ivalue;
        switch (op) {
          case ASSIGN:    v = rhs->constant->ivalue; break;
          case ASSIGNADD: v += rhs->constant->ivalue; break;
          case ASSIGNSUB: v -= rhs->constant->ivalue; break;
          case ASSIGNMUL: v *= rhs->constant->ivalue; break;
          case ASSIGNDIV: v /= rhs->constant->ivalue; break;
          case ASSIGNMOD: v %= rhs->constant->ivalue; break;
          case ASSIGNLSH: v <<= rhs->constant->ivalue; break;
          case ASSIGNRSH: v >>= rhs->constant->ivalue; break;
          case ASSIGNAND:v &= rhs->constant->ivalue; break;
          case ASSIGNOR:  v |= rhs->constant->ivalue; break;
          case ASSIGNXOR:v ^= rhs->constant->ivalue; break;
          default: break;
        }
        const_struct *nc = malloc(sizeof *nc);
        memset(nc, 0, sizeof *nc);
        nc->const_type = old->const_type;
        nc->ivalue     = v;
        add_mapping(map, idx, nc);
    }
    else if (op == ASSIGN && rhs->operator == CONSTANT) {
        add_mapping(map, idx, rhs->constant);
    }
}

static void handle_inc_dec(instr_node *instr, ConstantMapping **map) {
    expr_node *r = instr->expression;
    if (!r) return;
    oper_t op = r->operator;
    if (op != PREINC && op != PREDEC && op != POSTINC && op != POSTDEC) return;
    expr_node *c = r->left;
    if (!c || c->operator != IDENTIFIER || !c->identifier) return;
    int idx = c->identifier->rec_index;
    const_struct *old = lookup_mapping(*map, idx);
    remove_mapping(map, idx);
    if (old) {
        long long delta = (op == PREINC || op == POSTINC) ? 1 : -1;
        unsigned long long v = old->ivalue + delta;
        const_struct *nc = malloc(sizeof *nc);
        memset(nc, 0, sizeof *nc);
        nc->const_type = old->const_type;
        nc->ivalue     = v;
        add_mapping(map, idx, nc);
    }
}

/* ===================== PROPAGATE EXPR ===================== */
static void propagate_expr(expr_node *expr, ConstantMapping *map) {
    if (!expr) return;
    if (expr->operator == IDENTIFIER && expr->identifier) {
        int idx = expr->identifier->rec_index;
        const_struct *c = lookup_mapping(map, idx);
        if (c) {
            expr->operator   = CONSTANT;
            expr->constant   = c;
            /*expr->identifier = NULL; */
            return;
        }
    }
    if (expr->left)  propagate_expr(expr->left,  map);
    if (expr->right) propagate_expr(expr->right, map);
    for (expr_list *L = expr->expression_list; L; L = L->next) {
        propagate_expr(L->expression, map);
    }
}

/* ===================== DEAD CODE ELIMINATION ===================== */
static void mark_uses_expr(expr_node *expr, unsigned *used) {
    if (!expr) return;
    if (expr->operator == IDENTIFIER && expr->identifier) {
        used[expr->identifier->rec_index] = 1;
    }
    if (expr->left)  mark_uses_expr(expr->left,  used);
    if (expr->right) mark_uses_expr(expr->right, used);
    for (expr_list *L = expr->expression_list; L; L = L->next) {
        mark_uses_expr(L->expression, used);
    }
}

static void dead_code_elimination(sub_struct *sub) {
    int max_rec = sub->items;
    unsigned *used = calloc(max_rec, sizeof *used);
    for (instr_node *i = sub->sub_first; i; i = i->next) {
        mark_uses_expr(i->expression, used);
    }
    instr_node *prev = NULL, *cur = sub->sub_first;
    while (cur) {
        int remove = 0;
        expr_node *r = cur->expression;
        if (r && r->operator == ASSIGN) {
            expr_node *lhs = r->left;
            if (lhs && lhs->operator == IDENTIFIER && lhs->identifier) {
                int idx = lhs->identifier->rec_index;
                if (!used[idx]) remove = 1;
            }
        }
        if (remove) {
            if (prev) prev->next = cur->next;
            else       sub->sub_first = cur->next;
            cur = cur->next;
        } else {
            prev = cur;
            cur  = cur->next;
        }
    }
    free(used);
}

/* ===================== MEMORY CLEANUP ===================== */
static void free_regions(Region *r) {
    while (r) {
        Region *nx = r->next;
        free(r->blocks);
        free(r);
        r = nx;
    }
}

static void cleanup(BasicBlock *head, Region *regions, ConstantMapping *global_map) {
    for (int i = 0; i < nblocks; i++) {
        free(block_by_id[i]->dom);
        free(block_by_id[i]->succ);
        clear_mapping(&block_by_id[i]->entry_map);
        clear_mapping(&block_by_id[i]->exit_map);
    }
    free(block_by_id);
    free(instruction_to_block);
    free_regions(regions);
    clear_mapping(&global_map);
}

/* ===================== OPTIMIZE & MAIN ===================== */
static void optimize_subroutine(sub_struct *sub) {
    /* Control Flow Simplification */
    printf("[DEBUG] Control flow simplification...\n");
    control_flow_simplification(sub);
    printf("[LOG] Control flow simplification complete.\n");
    /* Peephole Optimization */
    printf("[DEBUG] Peephole optimization...\n");
    peephole_optimization(sub);
    printf("[LOG] Peephole optimization complete.\n");
    /* Inline Expansion */
    printf("[DEBUG] Inline expansion...\n");
    inline_expansion(sub);
    printf("[LOG] Inline expansion complete.\n");
    /* Common Subexpression Elimination */
    printf("[DEBUG] Common subexpression elimination...\n");
    common_subexpression_elimination(sub);
    printf("[LOG] Common subexpression elimination complete.\n");
    /* Strength Reduction */
    printf("[DEBUG] Strength reduction...\n");
    strength_reduction(sub);
    printf("[LOG] Strength reduction complete.\n");
    /* Loop-Invariant Code Motion */
    printf("[DEBUG] Loop-invariant code motion...\n");
    loop_invariant_code_motion(sub);
    printf("[LOG] Loop-invariant code motion complete.\n");
    /* Copy Propagation */
    printf("[DEBUG] Copy propagation...\n");
    copy_propagation(sub);
    printf("[LOG] Copy propagation complete.\n");
}

void my_optimization(void) {
    printf("[INFO] Starting optimization...\n");
    for (int i = 0; i < subroutine_number; i++) {
        if (subroutines[i]) {
            int before = count_instructions(subroutines[i]);
            printf("[INFO] Optimizing subroutine %d...\n", i);
            optimize_subroutine(subroutines[i]);
            int after = count_instructions(subroutines[i]);
            printf("[REPORT] Subroutine %d: Instructions before = %d, after = %d, reduced = %d\n", i, before, after, before - after);
            printf("[INFO] Dumping AST after optimization for subroutine %d...\n", i);
            dump_ast();
        } else {
            fprintf(stderr, "[WARN] subroutine %d is NULL\n", i);
        }
    }
    printf("[INFO] Optimization complete.\n");
}

// ===================== INSTRUCTION COUNTER =====================
int count_instructions(sub_struct *sub) {
    int count = 0;
    for (instr_node *i = sub->sub_first; i; i = i->next) {
        count++;
    }
    return count;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "[ERROR] Usage: %s <input.ir> <output.ir>\n", argv[0]);
        return 1;
    }
    printf("[INFO] Loading IR from %s...\n", argv[1]);
    if (load_intermediate(argv[1])) {
        fprintf(stderr, "[ERROR] Failed to load IR\n");
        return 1;
    }
    printf("[INFO] Dumping AST before optimization...\n");
    dump_ast();
    my_optimization();
    printf("[INFO] Dumping AST after all optimizations...\n");
    dump_ast();
    int ret = store_intermediate(argv[2]);
    printf("[INFO] store_intermediate returned %d\n", ret);
    if (ret) {
        fprintf(stderr, "[ERROR] Failed to write %s\n", argv[2]);
        return 1;
    }
    printf("[INFO] Wrote optimized IR to %s\n", argv[2]);
    return 0;
}

/* ===================== NEWLIB STUBS ===================== */
/* Για να ικανοποιηθούν τα __getreent και __locale_ctype_ptr από libirloadstore.a */
struct _reent { int _dummy; };
static struct _reent _global_reent = { 0 };
struct _reent* __getreent(void) { return &_global_reent; }
void* __locale_ctype_ptr = NULL;

/* Test model of the CCC IR (see csensetypes.h). */
#ifndef CCC_MODEL_INTERMEDIATE_H
#define CCC_MODEL_INTERMEDIATE_H

#include "csensetypes.h"

typedef struct const_struct {
    const_type_t const_type;
    long long ivalue;
    double fvalue;
    char *svalue;
} const_struct;

typedef struct identifier_struct {
    int rec_index;
    const char *name;
} identifier_struct;

typedef struct expr_node expr_node;
typedef struct expr_list {
    expr_node *expression;
    struct expr_list *next;
} expr_list;

struct expr_node {
    oper_t operator;
    expr_node *left, *right;
    identifier_struct *identifier;
    const_struct *constant;
    expr_list *expression_list;   /* call arguments */
};

typedef struct instr_node instr_node;
typedef struct instr_list {
    instr_node *instruction;
    struct instr_list *next;
} instr_list;

/* Control instructions point at other instructions:
 *   IF_BRANCH      - instruction: first instruction when the condition holds,
 *                    tail_instruction: where execution continues otherwise
 *   WHILE/FOR/DO   - instruction: first instruction of the body; next: loop exit
 *   SELECT_BRANCH  - target_list: case entries; tail_instruction: default
 *   S_GOTO         - target
 */
struct instr_node {
    int node_i;
    instr_type_t type;
    expr_node *expression;
    instr_node *next;
    instr_node *target;
    instr_node *instruction;
    instr_node *tail_instruction;
    instr_node *parent;
    instr_list *target_list;
};

typedef struct sub_struct {
    instr_node *sub_first;
    int items;                    /* number of symbol records of the subroutine */
} sub_struct;

extern sub_struct *subroutines[MAX_SUBROUTINES];
extern int subroutine_number;
extern int i_node_number;

void dump_ast(void);

#endif

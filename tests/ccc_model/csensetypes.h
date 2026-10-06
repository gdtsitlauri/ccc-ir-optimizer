/* Test model of the CCC IR types used by my_opt.c.
 *
 * The CCC toolchain (csensetypes.h, intermediate.h, irloadstore.h and
 * libirloadstore.a) is course software and is not distributed with this
 * repository. These three headers declare only the subset of the IR that the
 * optimizer touches - the same type, field and constant names - so that the
 * optimization passes can be compiled and unit-tested on hand-built IR.
 * The real build uses the CCC headers instead of this directory.
 */
#ifndef CCC_MODEL_CSENSETYPES_H
#define CCC_MODEL_CSENSETYPES_H

#define MAX_SUBROUTINES 64

typedef enum {
    TYPE_INT, TYPE_DOUBLE, TYPE_STRING
} const_type_t;

typedef enum {
    IDENTIFIER, CONSTANT, FUNCALL,
    PLUSOP, MINUSOP, MULOP, DIVOP, LSHIFT, RSHIFT, LTOP, GTOP, EQOP, ADDROF, DEREF,
    PREINC, PREDEC, POSTINC, POSTDEC,
    /* the assignment operators form a contiguous range ASSIGN .. ASSIGNXOR */
    ASSIGN, ASSIGNADD, ASSIGNSUB, ASSIGNMUL, ASSIGNDIV, ASSIGNMOD,
    ASSIGNLSH, ASSIGNRSH, ASSIGNAND, ASSIGNOR, ASSIGNXOR
} oper_t;

typedef enum {
    EXPRESSION, IF_BRANCH, WHILE_LOOP, FOR_LOOP, DO_LOOP, SELECT_BRANCH,
    S_GOTO, S_BREAK, S_CONTINUE, S_RETURN, S_LABEL
} instr_type_t;

#endif

/* newlib_stubs.c - lets libirloadstore.a (built against newlib) link with a
 * MinGW/MSVCRT toolchain.
 *
 * The library refers to two newlib internals:
 *   __getreent()          returns the per-thread reentrancy structure; the
 *                         library reaches errno through it (its first field)
 *   __locale_ctype_ptr()  returns the character-class table used by the
 *                         ctype.h macros (isdigit, isspace, ...)
 * Here __getreent returns a zero-filled structure that is large enough for
 * any field newlib defines, and __locale_ctype_ptr returns a table with the
 * newlib layout for the ASCII characters.
 */
#include <string.h>

static long long reent_storage[256];  /* 2 KiB, zero-initialised */

void *__getreent(void) { return reent_storage; }

/* newlib ctype flags */
#define CT_U 01
#define CT_L 02
#define CT_N 04
#define CT_S 010
#define CT_P 020
#define CT_C 040
#define CT_X 0100
#define CT_B 0200

static char ctype_table[1 + 256];

const char *__locale_ctype_ptr(void) {
    static int ready = 0;
    if (!ready) {
        memset(ctype_table, 0, sizeof ctype_table);
        for (int c = 0; c < 128; c++) {
            char f = 0;
            if (c >= 'A' && c <= 'Z') f |= CT_U;
            if (c >= 'a' && c <= 'z') f |= CT_L;
            if (c >= '0' && c <= '9') f |= CT_N;
            if ((c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f')) f |= CT_X;
            if (c == ' ' || (c >= '\t' && c <= '\r')) f |= CT_S;
            if (c < 32 || c == 127) f |= CT_C;
            if (c == ' ') f |= CT_B;
            if (c > 32 && c < 127 && !(f & (CT_U | CT_L | CT_N))) f |= CT_P;
            ctype_table[1 + c] = f;
        }
        ready = 1;
    }
    return ctype_table;  /* newlib indexes (table + 1)[c] */
}

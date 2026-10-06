/* native_cases.c - runs tests/cases.c compiled as ordinary C with the
 * inputs ir_interp generates, and prints lines in ir_interp's format, so that the
 * interpreter can be checked against a C compiler:
 *
 *   cc -fwrapv -O2 tests/native_cases.c -o native_cases
 *   native_cases 200 | sort > native.txt
 *   ir_interp cases.ir 200 1 all | grep " seed " | sed 's/ steps [0-9]*$//' | sort > interp.txt
 *   diff native.txt interp.txt
 *
 * (sorted, because the IR may list the functions in another order)
 *
 * -fwrapv gives signed overflow the wrap-around behaviour the interpreter uses.
 */
#include <stdio.h>
#include <stdlib.h>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif
#include "cases.c"

typedef long long i64;
typedef unsigned long long u64;

/* the input generator of ir_interp.c */
static u64 rng;
static u64 next_rand(void) {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
}
static i64 rand_value(void) {
    switch (next_rand() % 4) {
    case 0: return (i64)(next_rand() % 3);
    case 1: return (i64)(next_rand() % 17) - 8;
    case 2: return (i64)(next_rand() % 256);
    default: return (i64)(int)(unsigned)next_rand();
    }
}
static void seed_rng(int seed) {
    rng = 0x9E3779B97F4A7C15ULL ^ (u64)seed * 0x100000001B3ULL;
    for (int w = 0; w < 4; w++) next_rand();
}

#define BUF 4096
static int buf[BUF];
static void fill(void) { for (int c = 0; c < BUF; c++) buf[c] = (int)rand_value(); }
static int arg(void) { return (int)rand_value(); }

static void report(const char *name, int seed, i64 ret, int with_buf) {
    u64 h = 1469598103934665603ULL;
#define MIX(x) do { h ^= (u64)(x); h *= 1099511628211ULL; } while (0)
    MIX(ret);
    if (with_buf)
        for (int c = 0; c < BUF; c++) MIX((i64)buf[c]);
    printf("%s seed %d ok ret %lld state %016llx\n", name, seed, ret, h);
}

/* arguments are drawn in parameter order, as ir_interp does */
#define RUN1(f) do { seed_rng(s); int a = arg(); report(#f, s, f(a), 0); } while (0)
#define RUN2(f) do { seed_rng(s); int a = arg(); int b = arg(); report(#f, s, f(a, b), 0); } while (0)
#define RUN3(f) do { seed_rng(s); int a = arg(); int b = arg(); int c = arg(); report(#f, s, f(a, b, c), 0); } while (0)

int main(int argc, char **argv) {
    int runs = argc > 1 ? atoi(argv[1]) : 100;
#ifdef _WIN32
    _setmode(_fileno(stdout), _O_BINARY); /* "\n" line ends, as ir_interp writes */
#endif
    /* the order of the functions in cases.c, which is the order of the IR */
    for (int s = 1; s <= runs; s++) { seed_rng(s); int n = arg(); fill(); report("loop_invariant", s, loop_invariant(n, buf), 1); }
    for (int s = 1; s <= runs; s++) RUN1(loop_kill);
    for (int s = 1; s <= runs; s++) RUN2(loops_jumps);
    for (int s = 1; s <= runs; s++) RUN1(branches);
    for (int s = 1; s <= runs; s++) RUN2(switches);
    for (int s = 1; s <= runs; s++) RUN2(copies);
    for (int s = 1; s <= runs; s++) RUN2(cse_kill);
    for (int s = 1; s <= runs; s++) RUN1(sequenced);
    for (int s = 1; s <= runs; s++) { seed_rng(s); fill(); setp(buf); report("setp", s, 0, 1); }
    for (int s = 1; s <= runs; s++) RUN1(aliased);
    for (int s = 1; s <= runs; s++) RUN1(folding);
    for (int s = 1; s <= runs; s++) RUN1(chains);
    for (int s = 1; s <= runs; s++) RUN1(for_forms);
    for (int s = 1; s <= runs; s++) RUN3(invariant_exprs);
    for (int s = 1; s <= runs; s++) RUN2(variant_exprs);
    for (int s = 1; s <= runs; s++) RUN3(nested_invariant);
    for (int s = 1; s <= runs; s++) RUN1(iterative_gain);
    for (int s = 1; s <= runs; s++) RUN3(guarded_div);
    for (int s = 1; s <= runs; s++) RUN3(loop_in_switch);
    for (int s = 1; s <= runs; s++) RUN2(algebra);
    for (int s = 1; s <= runs; s++) {
        seed_rng(s);
        int a = arg(), b = arg();
        fill();
        report("cases_top", s, cases_top(a, b, buf), 1);
    }
    return 0;
}

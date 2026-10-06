# CCC IR Optimizer

**Can region-based data-flow analysis optimize the intermediate code of a high-level-synthesis compiler without ever changing what the program computes?**

`my_opt.c` is an optimizer for the intermediate representation (IR) of CCC, the C-to-hardware
high-level-synthesis toolchain used in the Compilers course of the University of Thessaly. It sits
between the two halves of the toolchain:

```
translator -irstore prog.c     C front end            ->  prog.ir
my_opt prog.ir                 this optimizer         ->  result.ir
translator result.ir           Ada / hardware back end ->  result.ada
```

It builds a control-flow graph for every subroutine, finds its loops and their region hierarchy
(Aho, Lam, Sethi, Ullman, *Compilers*, 2nd ed., section 9.7, Algorithm 9.52), and uses the region
summaries for constant propagation, followed by copy propagation, common-subexpression elimination and
dead-code elimination.

| part | what it does |
| --- | --- |
| control-flow graph | one node per instruction; edges for if, while, do, for, switch (with fall-through), break, continue, goto and return |
| dominators | iterative bit-vector algorithm (section 9.6.1) |
| natural loops | back edges whose head dominates their tail; loops with the same head merge (section 9.6.6) |
| region hierarchy | Algorithm 9.52: loop regions ordered from the innermost outwards; each region's summary, the set of variables it may define, is built from the summaries of the regions inside it and its own statements |
| region-based constant propagation and folding | facts flow through sequences, both branches of an if (meet = intersection) and the case labels of a switch; at the entry of a loop region its summary removes the facts of the variables it may define, so the facts at the loop head are found without iterating; integer expressions with constant operands are folded |
| copy propagation | after `x = y`, later uses of `x` become `y` |
| common-subexpression elimination | in `x = e; ... z = e;` the second becomes `z = x` |
| dead-code elimination | an assignment to a variable that is never read, with no side effect on the right-hand side, is removed; repeated until nothing changes |

## Safety rules

- Facts are kept only for local scalar integer variables whose address is never taken (`&x` appears
  nowhere in the subroutine). Such variables cannot change through pointers, arrays or calls, so stores
  and calls do not affect them.
- Variables are rewritten only where they are read: never on the left of an assignment, under `++` or
  `--`, or under `&`. A variable written inside an expression (`(x = 4, x)`, `c && (x = 9)`) loses its
  fact before the expression's reads are rewritten.
- Folding covers integer `+ - * / % << >> & | ^` and unary minus, only when the result fits in 32 bits;
  `/ % << >> & | ^` only for non-negative operands.
- Facts are discarded at goto targets, and a loop or switch that a goto can enter from outside has no
  facts at its exit.
- The shape of the tree never changes: nodes are rewritten in place, and a removed instruction becomes
  an empty expression instruction, a form the front end itself produces.

## How the CCC IR is read

The IR is a syntax tree, and several of its fields are unions whose meaning depends on the instruction
type; in other instruction types they hold leftover data, not NULL. The optimizer therefore reads each
field only for the instruction types that define it:

| instruction | fields |
| --- | --- |
| expression, return | `expression` (an empty instruction has none) |
| if | `expression` (condition), `instruction` (then), `tail_instruction` (else) |
| while, do | `expression` (condition), `instruction` (body) |
| for | `ex_list` (always three entries: initialization, condition, step; NULL when omitted), `tail_instruction` (body) |
| switch | `expression`; one body list, as in C, with the case labels (`target_list`) and the default (`tail_instruction`) pointing into it |
| break, continue | `target`: the loop or switch they leave or restart |
| goto | `target`: the statement it jumps to |

Local variables are referenced with `rec_index = -k` for entry `k` of the subroutine's locals table
(entry 0 is the function result); globals with `rec_index >= 0`. The front end does not fill in
`record.address_used` in the stored IR, so the optimizer computes the address-taken variables itself.

## Main results

All runs use the course's translator and IR library on the eight sample programs of the course and on
`tests/programs/cases.c`, which exercises each transformation and the situations where it must not apply.

1. **Optimization never changed what a program computes.** `tests/ir_interp.c` executes IR files. Every
   function of the nine programs was run 200 times on random inputs before and after optimization:
   8,200 runs, and every one gave the same return value and the same memory contents. (502 of them
   stop at the step limit or on an out-of-bounds access in the program itself, such as `SBYTE[I-1]`
   with `I = 0` in `PS_RANDOM`, and they stop in the same way after optimization.)
   (`results/toolchain.txt`)
2. **The interpreter computes what C computes.** `cases.c` compiled as ordinary C gives the same results
   as the interpreter on its IR, before and after optimization, in all 2,800 runs
   (`results/interpreter_vs_native.txt`).
3. **The test detects mistakes.** Ten versions of the optimizer with one rule broken each (no kill at loop
   entry, no meet at an if or a case label, a missing kill in copy propagation or CSE, address-taken
   variables tracked, ...) were all detected (`results/mutation.txt`).
4. **The optimized IR goes through the back end.** The translator produces Ada from the optimized IR of
   every program. The changes it shows are the expected ones: in `pythagoras_test`, `SIDE * SIDE` with
   `SIDE = 5` becomes `25` inside the loop; in `rsa`, an unused absolute value is removed; in `mpeg1`,
   copies through a temporary disappear (`results/ada_changes.txt`).
5. **Fewer operations are executed.** Counting executed instructions and expression nodes, the
   optimized IR does 9.0% less work in `rsa`, 1.4% in `pythagoras_test`, 0.2% in `mpeg1` and 7.4% in
   `cases.c`. The other sample programs take their constants as parameters and are unchanged.

The translator's Ada back end stops on a shift of a signed variable (`a << 2`), with or without
optimization; in `cases.c` the optimizer folds those shifts, so only its optimized IR translates
completely.

## Earlier versions

The first version (September 2025) declared a region hierarchy, region-level constant propagation and
several other passes, but its analyses were never called and some passes could corrupt the IR. A
rewrite in October 2026 was written against a model of the IR, before the course files were at hand;
on the real IR it read union fields that hold leftover data and did not know that switch bodies are
shared lists or that break and continue name their statement. This version is written and tested
against the real translator and IR library.

## Folder map

```
ccc-ir-optimizer/
  my_opt.c                 the optimizer (analyses, passes, main)
  newlib_stubs.c           two newlib functions the IR library needs when linked with MinGW
  tests/
    run_tests.sh           toolchain round trip and differential test
    ir_interp.c            IR interpreter used by the differential test
    native_cases.c         runs cases.c as C with the interpreter's inputs
    programs/cases.c       test program (cases.ir: its IR)
    mutation/              mutants.txt, mutate.py, run_mutation.sh
  results/                 logs of the runs above
```

## Building and running

The CCC translator and IR library (`csensetypes.h`, `intermediate.h`, `irloadstore.h`,
`libirloadstore.a`) are course software and are not part of this repository. The library was built
with newlib; `newlib_stubs.c` supplies the two newlib functions it needs when linked with a MinGW
compiler (gcc or `zig cc -target x86_64-windows-gnu`):

```bash
gcc -O2 -I<ccc>/inter_library my_opt.c newlib_stubs.c <ccc>/inter_library/libirloadstore.a -o my_opt
./my_opt prog.ir          # writes result.ir
```

Tests, with `<ccc>` holding `inter_library/` and the translator:

```bash
CCC=<ccc> tests/run_tests.sh <ccc>/tests/*.c tests/programs/cases.c
CCC=<ccc> tests/mutation/run_mutation.sh build/run/*/<program>.ir ...
gcc -fwrapv -O2 tests/native_cases.c -o native_cases && ./native_cases 200
```

## Author

George David Tsitlauri, University of Thessaly.

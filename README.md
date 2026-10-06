# CCC IR Optimizer

**Which classic optimizations can be applied to the intermediate code of a high-level-synthesis compiler without ever changing what the program does?**

`my_opt.c` is an optimizer for the intermediate representation (IR) produced by the CCC C front end,
part of the CCC high-level-synthesis toolchain used in the Compilers course of the University of
Thessaly. It reads an IR file, analyses and transforms every subroutine, and writes the optimized IR.

| part | what it does |
| --- | --- |
| analysis | basic blocks (leaders: first instruction, jump targets, instructions after control instructions), control-flow graph, dominators (iterative bit vectors), natural loops (back edges whose target dominates their source) |
| jump cleanup | removes a `goto` to the very next instruction |
| algebraic simplification | `x+0`, `0+x`, `x-0`, `x*1`, `1*x`, `x<<0` with integer constants |
| constant propagation | after `x = c`, uses of `x` become `c` |
| copy propagation | after `x = y`, uses of `x` become `y` |
| common-subexpression elimination | in `x = e; ... z = e;` the second becomes `z = x` |
| dead-code elimination | removes assignments to variables that are never read, when the right-hand side has no side effects; repeated until nothing changes |

## Safety rules

Every transformation is conservative; when in doubt, the IR is left unchanged.

- Constant propagation, copy propagation and common-subexpression elimination work on straight-line
  code: their facts are discarded at every instruction that another instruction points to (a
  possible jump target) and after every control instruction. They never cross a jump, whether the
  IR keeps branch and loop bodies in the main instruction list or in separate lists; both are
  processed.
- A function call, a store through a pointer or array element, or an assignment nested inside an
  expression discards all facts. A write to a variable discards the facts about it and about every
  expression that uses it.
- Uses are rewritten only as operands of `+ - * <<`, at the root of a right-hand side and in call
  arguments; never on a left-hand side, under `++`/`--`, or under any other operator such as
  address-of.
- Symbol records are never modified, and an instruction that another instruction points to is never
  removed.

## Main results

1. **The passes do what they claim.** 23 checks in 15 unit tests on hand-built IR cover each
   transformation and the cases where it must not apply: a call or a store through a pointer between
   definition and use, a jump target, a loop body, a redefined operand, address-of
   (`results/unit_tests.txt`).
2. **Optimization never changes behaviour.** 5,000 random programs with arithmetic, copies, calls
   that write through a pointer, pointer loads and stores, forward branches and counted loops were
   run by an interpreter before and after optimization. The optimizer changed 4,136 of them, and
   every one printed exactly the same sequence of values afterwards (`results/differential.txt`).
3. **The differential test detects real mistakes.** With the jump-target rule removed, 83 of 2,000
   programs behaved differently; with the kill-on-write rule of constant propagation removed, 87 did.

## Changes from the first version

The first version (September 2025) contained analyses that were never called and passes that could
change program behaviour. This version keeps the analyses and runs them, and replaces the passes:

| first version | problem | now |
| --- | --- | --- |
| dominator, loop, region and constant-propagation code was never called | listed features did not run | analysis runs on every subroutine; constant propagation is part of the pipeline |
| "merge consecutive blocks" freed every second of two consecutive statements | deleted code | removed; jump cleanup only removes a goto to the next instruction |
| copy propagation changed `rec_index` inside the shared symbol record and also rewrote left-hand sides, with no kill on redefinition | renamed variables everywhere | uses are rewritten by pointer, left-hand sides are never touched, writes kill facts |
| common-subexpression elimination shared the same expression node between statements, with no check for redefinitions | wrong values after an operand changed | `z = e` becomes `z = x` only while `x` and the operands of `e` are unchanged |
| loop-invariant code motion reordered list links | corrupted the instruction list | removed |
| strength reduction overwrote a possibly shared constant | changed other uses of the constant | removed |
| inline expansion copied the callee body after the call without removing the call or binding parameters | executed the callee twice, in the wrong scope | removed |

## Folder map

```
ccc-ir-optimizer/
  my_opt.c               the optimizer (analyses, passes, main)
  tests/
    test_opt.c           unit tests on hand-built IR
    fuzz_opt.c           differential test with an IR interpreter
    ccc_model/           declarations of the subset of the CCC IR that my_opt.c uses
  results/               logs of the tests above
```

## Building and running

With the CCC toolchain (its headers `csensetypes.h`, `intermediate.h`, `irloadstore.h` and the library
`libirloadstore.a`), build `my_opt.c` as in the course:

```bash
gcc -std=c11 -O2 -I<ccc>/include my_opt.c -L<ccc>/lib -lirloadstore -o my_opt
./my_opt input.ir output.ir
```

The CCC toolchain is course software and is not part of this repository. The tests therefore use
`tests/ccc_model/`, which declares only the IR types, fields and constants that `my_opt.c` uses:

```bash
gcc -std=c11 -O1 -Itests/ccc_model tests/test_opt.c -o test_opt && ./test_opt
gcc -std=c11 -O1 -Itests/ccc_model tests/fuzz_opt.c -o fuzz_opt && ./fuzz_opt 5000
```

## Author

George David Tsitlauri, University of Thessaly.

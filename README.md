# CCC IR Optimizer

**Can region-based and iterative data-flow analysis optimize the intermediate code of a high-level-synthesis compiler without ever changing what the program computes?**

An optimizer for the intermediate representation (IR) of CCC, the C-to-hardware high-level-synthesis
toolchain of the Compilers course (Advanced Topics in Compilers) of the University of Thessaly. It
fills the slot the toolchain leaves for a user optimizer:

```
translator -irstore prog.c     C front end              ->  prog.ir
my_opt prog.ir [-iterative]    this optimizer           ->  result.ir
translator result.ir           Ada back end             ->  result.ada
                               course server (ccc.cs.uowm.gr/ccc)  ->  VHDL / Verilog
```

## What it does

**Analysis** (Aho, Lam, Sethi, Ullman, *Compilers*, 2nd ed., chapter 9)

- a control-flow graph of every function: one node per instruction (three for a `for` loop:
  initialization, test, step), with if, while, do, for, switch (including fall-through), break,
  continue and return
- dominators, with the iterative bit-vector algorithm (section 9.6.1)
- natural loops, found from the back edges (section 9.6.6)
- the region hierarchy of Algorithm 9.52 (section 9.7): the loops are ordered from the innermost
  outwards, and each gets a summary of the variables it may change, built from the summaries of the
  loops inside it
- constant propagation computed two ways, both always run:
  - **region-based** (non-iterative): at a loop's entry the loop's summary says which constants
    survive, so the loop is never iterated over. This is the one applied by default.
  - **iterative** (sections 9.3 and 9.4): the classic algorithm on the control-flow graph, repeated
    until nothing changes. It is more precise, since it can see that a variable the loop rewrites still
    has the same value; option `-iterative` applies it instead.

  The two are compared on every run: each constant the region-based analysis finds must also be found
  by the iterative one, with the same value. A difference would mean a bug in one of them.

**Transformations**

| transformation | example |
| --- | --- |
| constant propagation and folding | `k = 4; ... t = k * 3;` becomes `t = 12`; `SIDE * SIDE` with `SIDE = 5` becomes `25` |
| algebraic simplification | `x + 0`, `x * 1`, `x - 0`, `x \| 0` become `x`; `x * 0` becomes `0` |
| loop-invariant code motion | `for (...) s = s + a * b;` becomes `t = a * b; for (...) s = s + t;` |
| copy propagation | after `x = y`, later uses of `x` read `y` |
| common-subexpression elimination | in `y = a + b; z = a + b;` the second becomes `z = y` |
| dead-code elimination | an assignment to a variable that is never read is removed |

## What it does not do, and why

| not done | why |
| --- | --- |
| inlining | the CCC front end already inlines on request (`-oinline`); the first version of this project did it wrongly and ran the called function twice |
| strength reduction (`x * 4` to `x << 2`) | the translator's Ada back end stops on a shift of a signed variable, so the optimized program could no longer be translated |
| optimizing floating-point values, arrays, pointers, structs or globals, or a local whose address is taken (`&x`) | these can change through pointers or calls; proving a change safe would need alias analysis, so the optimizer leaves them as they are |
| moving a division out of a loop | if the loop runs zero times, the moved division could divide by zero where the original program does not |
| the hardware step | the course server (ccc.cs.uowm.gr/ccc) did not respond, so the optimized programs were translated to Ada but not to VHDL/Verilog |

## Results

The test programs are the eight sample programs of the course and `tests/cases.c`, written to exercise
each transformation and the situations where it must not apply.

1. **Optimization never changed what a program computes.** `tests/ir_interp.c` executes IR files.
   Every function of the nine programs ran 200 times on random inputs, before and after optimization,
   in both modes: 9,600 runs per mode, and every one gave the same return value and the same memory
   contents (`results/toolchain.txt`). Runs that stop at the step limit or on an out-of-bounds access
   in the program itself, such as `SBYTE[I-1]` with `I = 0` in `PS_RANDOM`, stop the same way after
   optimization.
2. **The interpreter computes what C computes.** `cases.c` compiled as ordinary C gives the same results
   as the interpreter on its IR, original and optimized in both modes, in all 4,200 runs
   (`results/interpreter_vs_native.txt`).
3. **The tests catch mistakes.** Sixteen copies of the optimizer, each with one rule broken (no kill at
   loop entry, iterative analysis ignoring back edges, code motion of a variable the loop writes or of a
   division, `0 - x` simplified to `x`, ...), were all detected (`results/mutation.txt`).
4. **The two analyses agree.** On all nine programs, every constant found by the region-based analysis
   was found by the iterative one with the same value. In `cases.c` the iterative analysis finds 33
   constant uses and the region-based one 31; the two extra are a variable that a loop rewrites with the
   same value.
5. **The optimized programs do less work.** Counting executed instructions and expression nodes:

   | program | before | after | less work |
   | --- | --- | --- | --- |
   | `pythagoras_test` | 592,627,691 | 514,691,691 | 13.2% |
   | `rsa` | 5,164,362 | 4,699,062 | 9.0% |
   | `cases.c` (region-based / iterative) | 1,811,276 | 1,621,880 / 1,613,580 | 10.5% / 10.9% |
   | `integer_lib` | 22,198,589 | 22,129,944 | 0.3% |
   | `linedraw` | 1,205,786 | 1,202,676 | 0.3% |
   | `mpeg1` | 478,051 | 477,767 | 0.1% |

   `differential`, `fir` and `PS_RANDOM` take all their values as parameters and have nothing the
   optimizer can improve. In `mpeg1`, code motion also moves expressions out of branches that run
   rarely, so it gains less there than the other passes alone (0.2%).
6. **The optimized IR goes through the back end.** The translator produces Ada from the optimized IR of
   every program, in both modes (`results/ada_changes.txt` shows the changes). The translator stops on
   a shift of a signed variable (`a << 2`) even without optimization; in `cases.c` the optimizer folds
   those shifts, so only its optimized IR translates completely.

## Reading the CCC IR

The IR is a syntax tree whose fields are unions: a field that an instruction type does not use holds
leftover data, not NULL. The optimizer reads each field only where it is defined:

| instruction | fields |
| --- | --- |
| expression, return | `expression` (none for an empty instruction) |
| if | `expression` (condition), `instruction` (then), `tail_instruction` (else) |
| while, do | `expression` (condition), `instruction` (body) |
| for | `ex_list`: always three entries (initialization, condition, step), NULL when omitted; `tail_instruction` (body) |
| switch | `expression`; one body list, as in C, with the case labels (`target_list`) and the default (`tail_instruction`) pointing into it |
| break, continue | `target`: the loop or switch they leave or restart |

A local variable is referenced with `rec_index = -k` for entry `k` of the function's locals table (entry 0
is the result). The translator does not fill in `record.address_used`, so the optimizer finds the
address-taken variables itself. A new variable, such as a temporary of code motion, must also be counted
in `names_size`, the size of the name table the IR file stores. The translator does not accept `goto` or,
by default, global variables.

## Folder map

```
ccc-ir-optimizer/
  src/
    my_opt.c            the optimizer
    newlib_stubs.c      lets the course's IR library link with a MinGW compiler
  tests/
    run_tests.sh        translate, optimize in both modes, translate back, compare with the interpreter
    ir_interp.c         IR interpreter
    cases.c, cases.ir   test program and its IR
    native_cases.c      runs cases.c as C with the interpreter's inputs
    run_mutation.sh     mutation test: mutants.txt, applied by mutate.py
  results/              logs of the runs
```

## Building and running

The CCC translator and IR library (`csensetypes.h`, `intermediate.h`, `irloadstore.h`,
`libirloadstore.a`) are course software and are not included. With them in `<ccc>/inter_library` and
`<ccc>/translator`, and a MinGW compiler (gcc, or `zig cc -target x86_64-windows-gnu`):

```bash
gcc -O2 -I<ccc>/inter_library src/my_opt.c src/newlib_stubs.c <ccc>/inter_library/libirloadstore.a -o my_opt
./my_opt prog.ir                                    # region-based; writes result.ir
./my_opt prog.ir -iterative                         # iterative

CCC=<ccc> tests/run_tests.sh <ccc>/tests/*.c tests/cases.c
CCC=<ccc> tests/run_mutation.sh                     # after run_tests.sh
gcc -fwrapv -O2 tests/native_cases.c -o native_cases && ./native_cases 200
```

## Author

George David Tsitlauri, University of Thessaly.

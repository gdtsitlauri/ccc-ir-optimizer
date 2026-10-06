# CCC IR Optimizer

**Can region-based data-flow analysis optimize the intermediate code of a high-level-synthesis compiler without ever changing what the program computes?**

An optimizer for the intermediate representation (IR) of CCC, the C-to-hardware high-level-synthesis
toolchain of the Compilers course (Advanced Topics in Compilers) of the University of Thessaly. It
fills the slot the toolchain leaves for a user optimizer:

```
translator -irstore prog.c     C front end              ->  prog.ir
my_opt prog.ir                 this optimizer           ->  result.ir
translator result.ir           Ada back end             ->  result.ada
                               course server (ccc.cs.uowm.gr/ccc)  ->  VHDL / Verilog
```

## What it does

**Analysis** (Aho, Lam, Sethi, Ullman, *Compilers*, 2nd ed., chapter 9)

- a control-flow graph of every function, one node per instruction, with if, while, do, for, switch
  (including fall-through), break, continue and return
- dominators, with the iterative bit-vector algorithm (section 9.6.1)
- natural loops, found from the back edges (section 9.6.6)
- the region hierarchy of Algorithm 9.52 (section 9.7): the loops are ordered from the innermost
  outwards, and each gets a summary of the variables it may change, built from the summaries of the
  loops inside it

**Transformations**

| transformation | example |
| --- | --- |
| region-based constant propagation: at a loop's entry its summary says which constants survive, so no iteration over the loop is needed | in `k = 4; for (...) { t = k * 3; s = s + t + i; }` the loop body becomes `s = s + 12 + i` |
| constant folding | `SIDE * SIDE` with `SIDE = 5` becomes `25` |
| copy propagation | after `x = y`, later uses of `x` read `y` |
| common-subexpression elimination | in `y = a + b; z = a + b;` the second becomes `z = y` |
| dead-code elimination | an assignment to a variable that is never read is removed |

## What it does not do

- **No loop-invariant code motion, inlining, strength reduction or algebraic simplification** (`x + 0`).
  The first version of this project had the first three, and each one could break the program: code
  motion corrupted the instruction list, inlining ran the called function twice, strength reduction
  changed a constant that other expressions shared. They were removed rather than shipped broken.
- **Only integer variables.** Floating-point values, pointers, arrays, structs and globals are never
  rewritten, and neither is a local whose address is taken (`&x`); the optimizer leaves them as they are.
- **No iterative data-flow analysis** to set beside the region-based one; constant propagation is
  region-based only.
- **The hardware step was not run.** The optimized IR was translated to Ada for every program, but not
  sent to the course server for VHDL/Verilog.

## Results

The test programs are the eight sample programs of the course and `tests/cases.c`, written to exercise
each transformation and the situations where it must not apply.

1. **Optimization never changed what a program computes.** `tests/ir_interp.c` executes IR files. Every
   function of the nine programs ran 200 times on random inputs, before and after optimization: 8,200
   runs, all with the same return value and the same memory contents (`results/toolchain.txt`). 502 of
   them stop at the step limit or on an out-of-bounds access in the program itself, such as
   `SBYTE[I-1]` with `I = 0` in `PS_RANDOM`, and stop the same way after optimization.
2. **The interpreter computes what C computes.** `cases.c` compiled as ordinary C gives the same results
   as the interpreter on its IR, before and after optimization, in all 2,800 runs
   (`results/interpreter_vs_native.txt`).
3. **The test catches mistakes.** Ten copies of the optimizer, each with one rule broken (no kill at loop
   entry, no meet after an if, address-taken variables tracked, ...), were all detected
   (`results/mutation.txt`).
4. **The optimized IR goes through the back end.** The translator produces Ada from the optimized IR of
   every program (`results/ada_changes.txt` shows the changes).
5. **Less work at run time.** The optimized programs execute 9.0% fewer operations in `rsa`, 1.4% in
   `pythagoras_test`, 0.2% in `mpeg1` and 7.4% in `cases.c`. The other sample programs receive their
   values as parameters, so there is nothing to propagate and they are unchanged.

The translator's Ada back end stops on a shift of a signed variable (`a << 2`) even without
optimization. In `cases.c` the optimizer folds those shifts, so only its optimized IR translates
completely.

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
address-taken variables itself. The translator does not accept `goto` or, by default, global variables.

## Folder map

```
ccc-ir-optimizer/
  src/
    my_opt.c            the optimizer
    newlib_stubs.c      lets the course's IR library link with a MinGW compiler
  tests/
    run_tests.sh        translate, optimize, translate back, compare with the interpreter
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
./my_opt prog.ir                                    # writes result.ir

CCC=<ccc> tests/run_tests.sh <ccc>/tests/*.c tests/cases.c
CCC=<ccc> tests/run_mutation.sh                     # after run_tests.sh
gcc -fwrapv -O2 tests/native_cases.c -o native_cases && ./native_cases 200
```

## Author

George David Tsitlauri, University of Thessaly.

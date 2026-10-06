#!/bin/bash
# run_tests.sh - runs the optimizer on C programs through the CCC toolchain and
# checks that optimization does not change what they compute.
#
#   CCC=<ccc dir> [CC="<c compiler>"] [RUNS=200] tests/run_tests.sh prog.c|prog.ir ...
#
# <ccc dir> holds the course files: inter_library/ (csensetypes.h,
# intermediate.h, irloadstore.h, libirloadstore.a) and the translator executable
# (TRANSLATOR, default "<ccc dir>/translator/c-to-ada translator.exe").
#
# For each program:
#   1. translator -irstore prog.c       -> prog.ir   (skipped for a .ir input)
#   2. my_opt prog.ir                   -> region.ir    (region-based constant propagation)
#      my_opt prog.ir -iterative        -> iterative.ir (iterative constant propagation)
#   3. translator on all three          -> Ada; reports whether each translation completes
#   4. ir_interp on all three, every function, RUNS seeds each; any difference
#      from the original in return value or observable memory is a mismatch
# Work files go to build/run/<prog>/. Exit status 1 if any run mismatches.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
: "${CCC:?set CCC to the directory with inter_library/ and the translator}"
CC=${CC:-gcc}
RUNS=${RUNS:-200}
TRANSLATOR=${TRANSLATOR:-"$CCC/translator/c-to-ada translator.exe"}
LIB="$CCC/inter_library"
build="$here/build"
mkdir -p "$build/run"

$CC -O2 -I"$LIB" "$here/src/my_opt.c" "$here/src/newlib_stubs.c" "$LIB/libirloadstore.a" -o "$build/my_opt.exe" || exit 2
$CC -O2 -I"$LIB" "$here/tests/ir_interp.c" "$here/src/newlib_stubs.c" "$LIB/libirloadstore.a" -o "$build/ir_interp.exe" || exit 2

translated() { grep -q "translation completed" "$1" && echo completed || echo stopped; }
results() { "$build/ir_interp.exe" "$1" "$RUNS" 1 all | grep " seed " > "$2"; }
mismatches() { diff <(sed 's/ steps [0-9]*$//' "$1") <(sed 's/ steps [0-9]*$//' "$2") | grep -c '^<'; }
steps() { awk '/ ok /{s += $NF} END {print s + 0}' "$1"; }

status=0
for src in "$@"; do
    name=$(basename "$src"); name=${name%.*}
    work="$build/run/$name"
    mkdir -p "$work"
    case "$src" in
    *.c)
        cp "$src" "$work/$name.c"
        (cd "$work" && "$TRANSLATOR" -irstore "$name.c" > irstore.log 2>&1)
        ;;
    *)
        cp "$src" "$work/$name.ir"
        ;;
    esac
    if [ ! -f "$work/$name.ir" ]; then echo "$name: the translator did not produce IR"; status=1; continue; fi

    echo "== $name"
    for mode in region iterative; do
        flag=""; [ "$mode" = iterative ] && flag="-iterative"
        (cd "$work" && rm -f result.ir && "$build/my_opt.exe" "$name.ir" $flag > "opt_$mode.log" 2>&1 && mv result.ir "$mode.ir")
        if [ ! -f "$work/$mode.ir" ]; then echo "   $mode: my_opt failed"; status=1; continue 2; fi
    done
    (cd "$work" && for f in "$name" region iterative; do "$TRANSLATOR" "$f.ir" > "ada_$f.log" 2>&1; done)
    results "$work/$name.ir" "$work/run_orig.txt"
    sed -n 's/^\[REPORT\] /   /p' "$work/opt_region.log" | sed -n '1,2p'
    echo "   Ada translation: original $(translated "$work/ada_$name.log"), region $(translated "$work/ada_region.log"), iterative $(translated "$work/ada_iterative.log")"
    runs=$(wc -l < "$work/run_orig.txt")
    ok=$(grep -c " ok " "$work/run_orig.txt")
    for mode in region iterative; do
        results "$work/$mode.ir" "$work/run_$mode.txt"
        m=$(mismatches "$work/run_orig.txt" "$work/run_$mode.txt")
        [ "$m" -ne 0 ] && status=1
        echo "   $mode:"
        sed -n 's/^\[REPORT\] /      /p' "$work/opt_$mode.log" | sed -n '3,4p'
        echo "      interpreter: $runs runs ($ok complete), mismatches $m, steps $(steps "$work/run_orig.txt") -> $(steps "$work/run_$mode.txt")"
    done
done
exit $status

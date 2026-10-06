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
#   1. translator -irstore prog.c            -> prog.ir   (skipped for a .ir input)
#   2. my_opt prog.ir                        -> result.ir
#   3. translator on prog.ir and result.ir   -> Ada; reports whether each completes
#   4. ir_interp on prog.ir and result.ir, every function, RUNS seeds each;
#      any difference in return value or observable memory is a mismatch
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

    (cd "$work" && "$build/my_opt.exe" "$name.ir" > opt.log 2>&1)
    if [ ! -f "$work/result.ir" ]; then echo "$name: my_opt failed"; status=1; continue; fi

    (cd "$work" && "$TRANSLATOR" "$name.ir" > ada_orig.log 2>&1; "$TRANSLATOR" result.ir > ada_opt.log 2>&1)
    done_orig=$(grep -c "translation completed" "$work/ada_orig.log")
    done_opt=$(grep -c "translation completed" "$work/ada_opt.log")

    "$build/ir_interp.exe" "$work/$name.ir" "$RUNS" 1 all | grep " seed " > "$work/run_orig.txt"
    "$build/ir_interp.exe" "$work/result.ir" "$RUNS" 1 all | grep " seed " > "$work/run_opt.txt"
    mismatches=$(diff <(sed 's/ steps [0-9]*$//' "$work/run_orig.txt") <(sed 's/ steps [0-9]*$//' "$work/run_opt.txt") | grep -c '^<')
    runs=$(wc -l < "$work/run_orig.txt")
    ok=$(grep -c " ok " "$work/run_orig.txt")
    steps_orig=$(awk '/ ok /{s += $NF} END {print s + 0}' "$work/run_orig.txt")
    steps_opt=$(awk '/ ok /{s += $NF} END {print s + 0}' "$work/run_opt.txt")
    [ "$mismatches" -ne 0 ] && status=1

    echo "== $name"
    sed -n 's/^\[REPORT\] /   /p' "$work/opt.log"
    echo "   Ada translation: original $( [ "$done_orig" -gt 0 ] && echo completed || echo stopped ), optimized $( [ "$done_opt" -gt 0 ] && echo completed || echo stopped )"
    echo "   interpreter: $runs runs ($ok complete), mismatches $mismatches, steps $steps_orig -> $steps_opt"
done
exit $status

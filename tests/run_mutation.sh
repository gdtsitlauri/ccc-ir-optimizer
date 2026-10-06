#!/bin/bash
# run_mutation.sh - checks that the differential test detects mistakes.
#
#   CCC=<ccc dir> [CC="<c compiler>"] [PYTHON=python] [RUNS=50] [LIMIT=60] tests/run_mutation.sh [prog.ir ...]
#
# Builds my_opt.c once per mutant in mutants.txt, optimizes every program with it
# in both modes (region-based and -iterative) and compares the original and the
# mutant's result with ir_interp (every function, RUNS seeds). A mutant is
# detected when at least one run differs.
# Run tests/run_tests.sh first: it builds build/ir_interp.exe, and with no
# arguments the programs it translated (build/run/<prog>/<prog>.ir) are used.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
: "${CCC:?set CCC to the directory with inter_library/}"
CC=${CC:-gcc}
PYTHON=${PYTHON:-python}
RUNS=${RUNS:-50}
LIMIT=${LIMIT:-60}   # seconds per optimizer run
LIB="$CCC/inter_library"
interp="$here/build/ir_interp.exe"
[ -x "$interp" ] || { echo "build/ir_interp.exe missing: run tests/run_tests.sh first"; exit 2; }

if [ $# -eq 0 ]; then
    for d in "$here"/build/run/*/; do p=$(basename "$d"); [ -f "$d/$p.ir" ] && set -- "$@" "$d/$p.ir"; done
fi
[ $# -gt 0 ] || { echo "no programs: give .ir files or run tests/run_tests.sh first"; exit 2; }

detected=0; total=0
for name in $(grep -v '^#' "$here/tests/mutants.txt" | sed 's/@@.*//'); do
    m="$here/build/mutants/$name"
    mkdir -p "$m"
    "$PYTHON" "$here/tests/mutate.py" "$here/src/my_opt.c" "$here/tests/mutants.txt" "$name" "$m/my_opt.c" || exit 2
    $CC -O2 -w -I"$LIB" "$m/my_opt.c" "$here/src/newlib_stubs.c" "$LIB/libirloadstore.a" -o "$m/my_opt.exe" || exit 2
    sum=0; where=""
    for ir in "$@"; do
        prog=$(basename "$ir" .ir)
        mkdir -p "$m/$prog"
        cp "$ir" "$m/$prog/orig.ir"
        "$interp" "$m/$prog/orig.ir" "$RUNS" 1 all | grep " seed " | sed 's/ steps [0-9]*$//' > "$m/$prog/orig.txt"
        for mode in region iterative; do
            flag=""; [ "$mode" = iterative ] && flag="-iterative"
            (cd "$m/$prog" && rm -f result.ir && timeout "$LIMIT" "$m/my_opt.exe" orig.ir $flag > "opt_$mode.log" 2>&1)
            if [ ! -f "$m/$prog/result.ir" ]; then # a mutant that crashes or hangs counts as detected
                sum=$((sum + 1)); where="$where $prog/$mode:no-output"; continue
            fi
            "$interp" "$m/$prog/result.ir" "$RUNS" 1 all | grep " seed " | sed 's/ steps [0-9]*$//' > "$m/$prog/$mode.txt"
            n=$(diff "$m/$prog/orig.txt" "$m/$prog/$mode.txt" | grep -c '^<')
            sum=$((sum + n))
            [ "$n" -gt 0 ] && where="$where $prog/$mode:$n"
        done
    done
    total=$((total + 1))
    if [ "$sum" -gt 0 ]; then detected=$((detected + 1)); verdict=detected; else verdict=MISSED; fi
    printf '%-26s %-8s %5d differing runs%s\n' "$name" "$verdict" "$sum" "${where:+ (}${where# }${where:+)}"
done
echo "$detected of $total mutants detected"
[ "$detected" -eq "$total" ]

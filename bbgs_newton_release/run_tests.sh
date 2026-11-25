#!/bin/sh
set -eu
cd "$(dirname "$0")"
cc -O2 -std=c11 -Wall -Wextra -Werror -o bbgs_newton bbgs_newton.c
check() {
  terms="$1" q="$2" m="$3" expected="$4" prefix="test_run_$1"
  ./bbgs_newton --terms "$terms" --q "$q" --m "$m" --out "$prefix" > "$prefix.log"
  grep -F "Affine rational points over GF(2^$m): $expected" "$prefix.log" >/dev/null
  grep -F 'Basis status: PASS (all selected Newton/RR dimension checks passed)' "$prefix.log" >/dev/null
  test -s "$prefix.points.tsv"
  test -s "$prefix.basis.tsv"
  test -s "$prefix.meta.txt"
  echo "PASS terms=$terms q=$q m=$m points=$expected"
}
check 4 2 3 29
check 5 2 4 121
check 6 2 5 497
check 7 2 6 2017
check 8 2 7 8129
check 9 2 8 32641
check 10 2 9 130817
check 4 8 9 32705
check 5 4 8 16321
check 6 2 10 869
if ./bbgs_newton --terms 10 --q 2 --m 8 >/dev/null 2>&1; then
  echo "FAIL invalid field parameters were accepted" >&2; exit 1
else
  echo "PASS invalid field parameters rejected"
fi
./bbgs_newton --terms 6 --q 2 --m 10 --genus 120 --out test_genus120 > test_genus120.log
grep -F 'Selected basis-capable curve: a=1 b=4 genus=120' test_genus120.log >/dev/null
echo "PASS genus-targeted selection"
if ./bbgs_newton --terms 6 --q 2 --m 10 --genus 121 >/dev/null 2>&1; then
  echo "FAIL unsupported genus was accepted" >&2; exit 1
else
  echo "PASS unsupported genus reported"
fi

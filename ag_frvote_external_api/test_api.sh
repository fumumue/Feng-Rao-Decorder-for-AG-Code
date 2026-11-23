#!/bin/sh
set -eu
./external_caller 0 > test_0.log
./external_caller 1 > test_1.log
./external_caller 2 > test_2.log
grep -q 'API return=0, recovered=0, expected=0' test_0.log
grep -q 'API return=0, recovered=1, expected=1' test_1.log
grep -q 'error\[0\]: position=5 value=7' test_1.log
grep -q 'API return=0, recovered=2, expected=2' test_2.log
grep -q 'error\[0\]: position=5 value=7' test_2.log
grep -q 'error\[1\]: position=99 value=31' test_2.log
echo 'API tests passed: 0, 1, and 2 errors.'

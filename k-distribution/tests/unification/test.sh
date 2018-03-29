#!/usr/bin/env bash

set -e

KOMPILE=../../target/release/k/bin/kompile
KRUN=../../target/release/k/bin/krun
TESTS=(basic)

tmp_out=$(mktemp output.XXXXX)
trap "rm -rf $tmp_out" INT TERM EXIT

$KOMPILE --backend java test.k

for test in $TESTS; do
    echo "== running: $test.test"
    $KRUN $test.test > $tmp_out
    git diff --no-index $test.out $tmp_out
done

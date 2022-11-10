DEF=test
EXT=test
TESTDIR=.
KOMPILE_FLAGS+=--gen-bison-parser --bison-stack-max-depth 12000
KRUN_FLAGS=--dry-run --no-expand-macros 1>/dev/null 2>/dev/null

include ../../../include/kframework/ktest.mak

# output is already ignored, no need to update results
update-results: CHECK=| diff -

DEF=test
EXT=test
TESTDIR=.
KOMPILE_FLAGS+=--gen-bison-parser --bison-stack-max-depth 12000
KRUN_FLAGS=--dry-run 1>/dev/null
# TODO: Don't disable pipefail in final version
PIPEFAIL=

include ../../../include/kframework/ktest.mak

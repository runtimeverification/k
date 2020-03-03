DEF=verif
EXT=verif
TESTDIR=.
KOMPILE_BACKEND=haskell
KPROVE_FLAGS=-m VERIFICATION
include ../../../include/ktest.mak


KORE_EXEC=$(abspath $(MAKEFILE_PATH)/../bin/kore-exec)
test-spec.k: kompile
	 rm -rf .kprove*
	 $(KPROVE) $@ $(KPROVE_FLAGS) -d $(DEFDIR) --debug --dry-run
	 mv .kprove* .kprove
	 $(KORE_EXEC)  .kprove/vdefinition.kore --module VERIFICATION --prove .kprove/spec.kore --spec-module TEST-SPEC | $(KAST) -i kore -o pretty -d .kprove /dev/stdin $(CHECK) $@.out
	 rm -rf .kprove






DEF=verif
EXT=verif
TESTDIR=.
KOMPILE_BACKEND=haskell
KPROVE_FLAGS=-m VERIFICATION
include ../../../include/kframework/ktest.mak


KORE_EXEC=$(abspath $(MAKEFILE_PATH)/../../bin/kore-exec)
test-spec.k: kompile
	 rm -rf .kprove* .prove
	 $(KPROVE) $@ $(KPROVE_FLAGS) -d $(DEFDIR) --debug --dry-run --save-proof-definition-to .prove
	 mv .kprove* .kprove
	 $(KORE_EXEC)  .kprove/vdefinition.kore --module VERIFICATION --prove .kprove/spec.kore --spec-module TEST-SPEC | $(KAST) -i kore -o pretty -d .prove /dev/stdin $(CHECK) $@.out
	 rm -rf .kprove .prove






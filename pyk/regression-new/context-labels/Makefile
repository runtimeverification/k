DEF=context
TESTDIR=.
KOMPILE_BACKEND=haskell
KPROVE_FLAGS+=--debugger --debug-script context-spec.k.in
KORE_REPL_OPTS=--log-entries DebugAppliedLabeledRewriteRule
export KORE_REPL_OPTS
CONSIDER_PROVER_ERRORS=2>&1 | sed 's!\[[0-9][0-9]*]!!g' # Hacking in a sed command here to remove strings of the form '[23452]'

include ../include/ktest.mak

K_RULE_FIND=${K_BIN}/k-rule-find

FIND_RULES_TESTS?=$(wildcard $(TESTDIR)/*.find-rule)

.PHONY: find-rules

all: find-rules

find-rules: $(FIND_RULES_TESTS)

%.find-rule: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(K_RULE_FIND) $(KOMPILED_DIR) $(shell cat $@) $(CHECK) $@.out
else
	$(K_RULE_FIND) $(KOMPILED_DIR) $(shell cat $@) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif


DEF=context
TESTDIR=.
KOMPILE_BACKEND=haskell
KPROVE_FLAGS+=--debugger --debug-script context-spec.k.in
KORE_REPL_OPTS=--log-entries DebugAppliedLabeledRewriteRule
export KORE_REPL_OPTS
CONSIDER_PROVER_ERRORS=2>&1 | sed 's!\[[0-9]\+]!!g' # Hacking in a sed command here to remove strings of the form '[23452]'

include ../../../include/kframework/ktest.mak

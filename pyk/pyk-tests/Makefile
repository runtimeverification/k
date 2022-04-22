K_ROOT := $(abspath ../..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast
KRUN    = $(K_BIN)/krun
KPROVE  = $(K_BIN)/kprove
KPROVEX = $(K_BIN)/kprovex
PYK     = pyk

export PATH := $(K_BIN):$(PATH)

CHECK = git --no-pager diff --no-index -R


.PHONY: all clean update-results \
        test test-kpyk test-kpyk-graphviz test-kpyk-minimize-term

all: test

clean:
	rm -rf definitions

update-results: CHECK=cp
update-results: test
kompile: $(llvm_imp_kompiled) $(haskell_imp_kompiled)


# Tests

test: test-kpyk

## kpyk runner tests

test-kpyk: test-kpyk-graphviz test-kpyk-minimize-term

test-kpyk-graphviz: imp-verification/haskell.kompiled
	$(PYK) definitions/imp-verification/haskell/imp-verification-kompiled graph-imports
	cat definitions/imp-verification/haskell/imp-verification-kompiled/import-graph | tr -cd '[:alnum:]\n' | grep . | tr '[:lower:]' '[:upper:]' | sort > import-graph.sorted
	$(CHECK) import-graph.sorted imp-import-graph.expected

test-kpyk-minimize-term: imp-verification/haskell.kompiled
	$(PYK) definitions/imp-verification/haskell/imp-verification-kompiled prove ../k-files/imp-verification.k ../k-files/imp-unproveable-spec.k IMP-UNPROVEABLE-SPEC \
	    | $(PYK) definitions/imp-verification/haskell/imp-verification-kompiled print /dev/stdin > imp-unproveable-spec.k.out
	$(CHECK) imp-unproveable-spec.k.out imp-unproveable-spec.k.expected


## definitions to build ahead of time

KOMPILE_BACKEND  = haskell
KOMPILE_COVERAGE =
KOMPILE_OPTS     =

definitions := imp-verification/haskell

build-definitions: $(definitions:=.kompiled)

%.kompiled:
	$(KOMPILE) --directory definitions/$*    \
	    -I k-files                           \
	    --backend $(KOMPILE_BACKEND)         \
	    --emit-json $(KOMPILE_COVERAGE)      \
	    $(KOMPILE_OPTS)                      \
	    ../k-files/$(patsubst %/,%,$(dir $@)).k

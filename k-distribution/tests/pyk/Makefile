K_RELEASE := $(abspath ../../target/release/k)
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib/kframework

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast
KRUN    = $(K_BIN)/krun
KPROVE  = $(K_BIN)/kprove
KPROVEX = $(K_BIN)/kprovex
KPYK    = $(K_BIN)/kpyk

export PATH := $(K_BIN):$(PATH)

CHECK = git --no-pager diff --no-index -R

PYTHONPATH := $(K_LIB)
export PYTHONPATH

.PHONY: all clean update-results pyk                         \
        test test-defn test-defn-kast test-defn-prove        \
        test-kpyk test-kpyk-graphviz test-kpyk-minimize-term \
        test-pytest

all: test

clean:
	rm -rf definitions specs

update-results: CHECK=cp
update-results: test
kompile: $(llvm_imp_kompiled) $(haskell_imp_kompiled)

# Tests

test: test-kpyk test-pytest

## kpyk runner tests

test-kpyk: test-kpyk-graphviz test-kpyk-minimize-term

test-kpyk-graphviz: $(llvm_imp_kompiled)
	$(KPYK) $(dir $<) graph-imports
	cat $(dir $<)import-graph | tr -cd '[:alnum:]\n' | grep . | tr '[:lower:]' '[:upper:]' | sort > import-graph.sorted
	$(CHECK) import-graph.sorted imp-import-graph.expected

test-kpyk-minimize-term: kpyk-tests/minimize/test.k
	$(KOMPILE) kpyk-tests/minimize/test.k --directory kpyk-tests/minimize --backend haskell --emit-json \
	    --main-module TEST
	$(KPYK) kpyk-tests/minimize/test-kompiled prove kpyk-tests/minimize/test.k kpyk-tests/minimize/test.k TEST-SPEC \
	    | $(KPYK) kpyk-tests/minimize/test-kompiled print /dev/stdin > kpyk-tests/minimize/test.k.out
	$(CHECK) kpyk-tests/minimize/test.k.out kpyk-tests/minimize/test.k.expected

## pytests

FILE_DEPS =

pytests = defn_test.py           \
          emit_json_spec_test.py \
          unit_test.py

defn_test.py.pytest:           FILE_DEPS = imp-verification/haskell.kompiled
emit_json_spec_test.py.pytest: FILE_DEPS = imp-verification/looping-spec.json.json-spec

test-pytest: $(pytests:=.pytest)

.SECONDEXPANSION:
%.pytest: % $$(FILE_DEPS)
	python3 -m unittest $<

## proofs to turn to json ahead of time

KPROVEX_DEFN =
KPROVEX_OPTS =
KPROVEX_FILE =

json_specs := imp-verification/looping-spec.json

imp-verification/looping-spec.json.json-spec: KPROVEX_DEFN = imp-verification/haskell
imp-verification/looping-spec.json.json-spec: KPROVEX_FILE = looping-spec.k

build-specs: $(json_specs:=.json-spec)

.SECONDEXPANSION:
%.json-spec: $$(KPROVEX_DEFN).kompiled
	$(KPROVEX) k-files/$(KPROVEX_FILE)          \
	    -I k-files                              \
	    --backend haskell --dry-run             \
	    --directory definitions/$(KPROVEX_DEFN) \
	    --emit-json-spec specs/$*               \
	    $(KPROVEX_OPTS)

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
	    k-files/$(patsubst %/,%,$(dir $@)).k

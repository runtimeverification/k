K_ROOT := $(abspath ../../..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast
KRUN    = $(K_BIN)/krun
KPROVE  = $(K_BIN)/kprove
KPROVEX = $(K_BIN)/kprovex
PYK     = pyk

export PATH := $(K_BIN):$(PATH)

CHECK = git --no-pager diff --no-index -R

export PYTHONPATH

.PHONY: all clean update-results pyk                         \
        test test-defn test-defn-kast test-defn-prove        \
        test-kpyk test-kpyk-graphviz test-kpyk-minimize-term \
        test-pytest

all: test

clean:
	rm -rf definitions specs
	rm -rf venv

update-results: CHECK=cp
update-results: test
kompile: $(llvm_imp_kompiled) $(haskell_imp_kompiled)


# Virtualenv

VENV     := venv/pyvenv.cfg
ACTIVATE := . venv/bin/activate

$(VENV):
	virtualenv -p python3.8 venv && $(ACTIVATE) && pip install -e $(K_ROOT)/pyk

# Tests

test: test-kpyk test-pytest

## kpyk runner tests

test-kpyk: test-kpyk-graphviz test-kpyk-minimize-term

test-kpyk-graphviz: imp-verification/haskell.kompiled $(VENV)
	$(ACTIVATE) && $(PYK) definitions/imp-verification/haskell/imp-verification-kompiled graph-imports
	cat definitions/imp-verification/haskell/imp-verification-kompiled/import-graph | tr -cd '[:alnum:]\n' | grep . | tr '[:lower:]' '[:upper:]' | sort > import-graph.sorted
	$(CHECK) import-graph.sorted imp-import-graph.expected

test-kpyk-minimize-term: imp-verification/haskell.kompiled $(VENV)
	$(ACTIVATE) && $(PYK) definitions/imp-verification/haskell/imp-verification-kompiled prove k-files/imp-verification.k k-files/imp-unproveable-spec.k IMP-UNPROVEABLE-SPEC \
	    | $(PYK) definitions/imp-verification/haskell/imp-verification-kompiled print /dev/stdin > imp-unproveable-spec.k.out
	$(CHECK) imp-unproveable-spec.k.out imp-unproveable-spec.k.expected

## pytests

FILE_DEPS =

pytests = $(wildcard *_test.py)

configuration_test.py.pytest:  FILE_DEPS = imp-verification/haskell.kompiled
defn_test.py.pytest:           FILE_DEPS = imp-verification/haskell.kompiled
emit_json_spec_test.py.pytest: FILE_DEPS = imp-verification/looping-spec.json.json-spec
parse_kast_test.py.pytest:     FILE_DEPS = contextual-function/haskell.kompiled \
                                           sort-synonym/haskell.kompiled
simple_proofs_test.py.pytest:  FILE_DEPS = simple-proofs/haskell.kompiled

test-pytest: $(pytests:=.pytest)

.SECONDEXPANSION:
%.pytest: % $$(FILE_DEPS) $(VENV)
	$(ACTIVATE) && python3 -m unittest $<

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

definitions := contextual-function/haskell \
               imp-verification/haskell    \
               simple-proofs/haskell       \
               sort-synonym/haskell

build-definitions: $(definitions:=.kompiled)

%.kompiled:
	$(KOMPILE) --directory definitions/$*    \
	    -I k-files                           \
	    --backend $(KOMPILE_BACKEND)         \
	    --emit-json $(KOMPILE_COVERAGE)      \
	    $(KOMPILE_OPTS)                      \
	    k-files/$(patsubst %/,%,$(dir $@)).k

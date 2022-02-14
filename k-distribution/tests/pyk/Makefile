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

.PHONY: all clean update-results pyk                                                \
        test test-defn test-defn-kast test-defn-prove                               \
        test-kpyk test-kpyk-coverage-log test-kpyk-graphviz test-kpyk-minimize-term \
        test-pytest

all: test

clean:
	rm -rf $(llvm_dir) $(haskell_dir) emit-json-spec-tests/verification-kompiled emit-json-spec-tests/looping-spec.json
	rm -rf definitions specs

llvm_dir          := llvm
llvm_imp          := $(llvm_dir)/imp.k
llvm_imp_kompiled := $(llvm_dir)/imp-kompiled/compiled.json

haskell_dir          := haskell
haskell_imp          := $(haskell_dir)/imp.k
haskell_imp_kompiled := $(haskell_dir)/imp-kompiled/compiled.json

%/imp.k: imp.k
	mkdir -p $*
	cp $< $@

$(llvm_imp_kompiled): $(llvm_imp) $(KOMPILE)
	$(KOMPILE) --directory $(llvm_dir) --backend llvm -I $(llvm_dir) $< --emit-json --coverage

$(haskell_imp_kompiled): $(haskell_imp) $(KOMPILE)
	$(KOMPILE) --directory $(haskell_dir) --backend haskell $< --emit-json

update-results: CHECK=cp
update-results: test
kompile: $(llvm_imp_kompiled) $(haskell_imp_kompiled)

# Tests

test: test-unit test-defn test-kpyk test-emit-json-spec

## Unit Tests

test-unit:
	python3 unit-test.py

## Full Definition Tests

test-defn: test-defn-kast test-defn-prove

defn_tests = defn-tests

pyk_kast_tests  = $(wildcard $(defn_tests)/kast-tests/*.json)
pyk_prove_tests = $(wildcard $(defn_tests)/proof-tests/*-spec.json)

test-defn-kast:  $(pyk_kast_tests:=.kast)
test-defn-prove: $(pyk_prove_tests:=.prove)

$(defn_tests)/kast-tests/%.gen: $(defn_tests)/build-config.py $(llvm_imp_kompiled) $(defn_tests)/kast-tests/%.json
	python3 $^ > $@

$(defn_tests)/proof-tests/%-spec.k: $(defn_tests)/build-config.py $(haskell_imp_kompiled) $(defn_tests)/proof-tests/%-spec.json
	python3 $^ > $@

$(defn_tests)/kast-tests/%.json.kast: $(defn_tests)/kast-tests/%.out
	git --no-pager diff --no-index $(defn_tests)/kast-tests/$*.expected $(defn_tests)/kast-tests/$*.out

$(defn_tests)/kast-tests/%.out: $(defn_tests)/kast-tests/%.gen $(llvm_imp_kompiled)
	$(KAST) --directory $(llvm_dir) --output pretty --sort $(basename $(basename $*)) -m IMP $< > $@

$(defn_tests)/proof-tests/%-spec.json.prove: $(defn_tests)/proof-tests/%-spec.k $(haskell_imp_kompiled)
	$(KPROVE) --directory $(haskell_dir) $< -m IMP -I $(haskell_dir)

## kpyk runner tests

sum_to_n_coverage := kpyk-tests/sum-to-n.imp.coverage

test-kpyk: test-kpyk-graphviz test-kpyk-coverage-log test-kpyk-minimize-term

test-kpyk-graphviz: $(llvm_imp_kompiled)
	$(KPYK) $(dir $<) graph-imports
	cat $(dir $<)import-graph | tr -cd '[:alnum:]\n' | grep . | tr '[:lower:]' '[:upper:]' | sort > import-graph.sorted
	$(CHECK) import-graph.sorted imp-import-graph.expected

$(sum_to_n_coverage): $(llvm_imp_kompiled) kpyk-tests/sum-to-n.imp
	rm -rf $(llvm_dir)/imp-kompiled/*_coverage.txt
	$(KRUN) --directory $(llvm_dir) kpyk-tests/sum-to-n.imp
	mv $(llvm_dir)/imp-kompiled/*_coverage.txt $@

test-kpyk-coverage-log: $(sum_to_n_coverage)
	$(KPYK) $(llvm_dir)/imp-kompiled coverage $(sum_to_n_coverage) > /dev/null

test-kpyk-minimize-term: kpyk-tests/minimize/test.k
	$(KOMPILE) kpyk-tests/minimize/test.k --directory kpyk-tests/minimize --backend haskell --emit-json \
	    --main-module TEST
	$(KPYK) kpyk-tests/minimize/test-kompiled prove kpyk-tests/minimize/test.k kpyk-tests/minimize/test.k TEST-SPEC \
	    | $(KPYK) kpyk-tests/minimize/test-kompiled print /dev/stdin > kpyk-tests/minimize/test.k.out
	$(CHECK) kpyk-tests/minimize/test.k.out kpyk-tests/minimize/test.k.expected

## pytests

FILE_DEPS =

pytests = defn_test.py           \
          emit_json_spec_test.py

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

definitions := imp/llvm                 \
               imp/haskell              \
               imp-verification/haskell

imp/llvm.kompiled: KOMPILE_BACKEND  = llvm
imp/llvm.kompiled: KOMPILE_COVERAGE = --coverage

build-definitions: $(definitions:=.kompiled)

%.kompiled:
	$(KOMPILE) --directory definitions/$*    \
	    -I k-files                           \
	    --backend $(KOMPILE_BACKEND)         \
	    --emit-json $(KOMPILE_COVERAGE)      \
	    $(KOMPILE_OPTS)                      \
	    k-files/$(patsubst %/,%,$(dir $@)).k

K_RELEASE := $(abspath ../../target/release/k)
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast
KPROVE  = $(K_BIN)/kprove

KOMPILE_BACKEND?=java

PYTHONPATH := $(K_LIB)
export PYTHONPATH

.PHONY: all clean pyk                                 \
        test test-defn test-defn-kast test-defn-prove

all: test

clean:
	rm -rf *-kompiled

imp_kompiled:=imp-kompiled/compiled.txt

$(imp_kompiled): imp.k $(KOMPILE)
	$(KOMPILE) --backend $(KOMPILE_BACKEND) -I . $< --emit-json

# Tests

test: test-unit test-defn

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

$(defn_tests)/kast-tests/%.gen: $(defn_tests)/build-config.py $(defn_tests)/kast-tests/%.json $(imp_kompiled)
	python3 $^ > $@

$(defn_tests)/proof-tests/%-spec.k: $(defn_tests)/build-config.py $(defn_tests)/proof-tests/%-spec.json $(imp_kompiled)
	python3 $^ > $@

$(defn_tests)/kast-tests/%.json.kast: $(defn_tests)/kast-tests/%.out
	git --no-pager diff --no-index $(defn_tests)/kast-tests/$*.expected $(defn_tests)/kast-tests/$*.out

$(defn_tests)/kast-tests/%.out: $(defn_tests)/kast-tests/%.gen $(imp_kompiled)
	$(KAST) --output pretty --sort $(basename $(basename $*)) -m IMP $< > $@

$(defn_tests)/proof-tests/%-spec.json.prove: $(defn_tests)/proof-tests/%-spec.k $(imp_kompiled)
	$(KPROVE) $< -m IMP

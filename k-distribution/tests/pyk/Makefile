K_RELEASE := $(abspath ../../target/release/k)
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast
KPROVE  = $(K_BIN)/kprove

KOMPILE_BACKEND?=java

PYTHONPATH := $(K_LIB)
export PYTHONPATH

.PHONY: all clean pyk test-kast test-prove

all: test-kast test-prove

clean:
	rm -rf *-kompiled

imp_kompiled:=imp-kompiled/compiled.txt

$(imp_kompiled): imp.k $(KOMPILE)
	$(KOMPILE) --backend $(KOMPILE_BACKEND) -I . $< --emit-json

kast-tests/%.gen: build-config.py kast-tests/%.json $(imp_kompiled)
	python3 $^ > $@

proof-tests/%-spec.k: build-config.py proof-tests/%-spec.json $(imp_kompiled)
	python3 $^ > $@

pyk_kast_tests = $(wildcard kast-tests/*.json)

kast-tests/%.json.kast: kast-tests/%.out
	git --no-pager diff --no-index kast-tests/$*.expected kast-tests/$*.out

kast-tests/%.out: kast-tests/%.gen $(imp_kompiled)
	$(KAST) --output pretty --sort $(basename $(basename $*)) -m IMP $< > $@

test-kast: $(pyk_kast_tests:=.kast)

pyk_prove_tests = $(wildcard proof-tests/*-spec.json)

proof-tests/%-spec.json.prove: proof-tests/%-spec.k $(imp_kompiled)
	$(KPROVE) $< -m IMP

test-prove: $(pyk_prove_tests:=.prove)

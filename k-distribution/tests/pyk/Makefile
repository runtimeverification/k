K_RELEASE := $(abspath ../../target/release/k)
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast

PYTHONPATH := $(K_LIB)/py-kframework
export PYTHONPATH

.PHONY: all clean pyk test-kast

all: test-kast

clean:
	rm -rf *-kompiled kast-tests/*.out kast-tests/*.gen

imp_kompiled:=imp-kompiled/compiled.bin

$(imp_kompiled): imp.k $(KOMPILE)
	$(KOMPILE) --backend kore $<

pyk_kast_tests = $(wildcard kast-tests/*.json)

kast-tests/%.json.kast: kast-tests/%.out
	git --no-pager diff --no-index kast-tests/$*.expected kast-tests/$*.out

kast-tests/%.out: kast-tests/%.gen $(imp_kompiled)
	$(KAST) --output pretty --sort $(basename $(basename $*)) -m IMP $< > $@

kast-tests/%.gen: build-config.py kast-tests/%.json
	python3 $< kast-tests/$*.json > kast-tests/$*.gen

test-kast: $(pyk_kast_tests:=.kast)

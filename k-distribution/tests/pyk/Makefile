K_RELEASE := $(abspath ../../target/release/k)
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib

KOMPILE = $(K_BIN)/kompile
KAST    = $(K_BIN)/kast

PYTHONPATH := $(K_LIB)/py-kframework
export PYTHONPATH

.PHONY: all clean pyk

all: pyk

clean:
	rm -rf *-kompiled *.out

imp_kompiled:=imp-kompiled/compiled.bin

pyk: build-config.out $(imp_kompiled)
	$(KAST) --output pretty --sort TCell -m IMP $<

build-config.out: build-config.py
	python3 $< > $@

$(imp_kompiled): imp.k $(KOMPILE)
	$(KOMPILE) --backend kore $<

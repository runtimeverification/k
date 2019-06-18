K_RELEASE := $(abspath ../../target/release/k)
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib

KOMPILE = $(K_BIN)/kompile
KRUN    = $(K_BIN)/krun
KPROVE  = $(K_BIN)/kprove
KAST    = $(K_BIN)/kast

PATH := $(PATH):$(K_BIN)
export PATH

PYTHONPATH := $(K_LIB)/py-kframework
export PYTHONPATH

all: pyk

imp_kompiled:=imp-kompiled/interpreter

pyk: build-config.out $(imp_kompiled)
	kast --output pretty --sort TCell $<

build-config.out:
	python3 build-config.py > build-config.out

$(imp_kompiled): imp.k $(KOMPILE)
	$(KOMPILE) --backend llvm $<

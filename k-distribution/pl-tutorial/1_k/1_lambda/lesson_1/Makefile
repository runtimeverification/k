MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=lambda
EXT=lambda
KOMPILE_FLAGS=--gen-glr-bison-parser

%/arithmetic-div-zero.lambda:
	true

include $(MAKEFILE_PATH)/../../../find-k.mak
include ${K_HOME}/include/kframework/ktest.mak

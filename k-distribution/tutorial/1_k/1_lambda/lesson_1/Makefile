MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=lambda
EXT=lambda
KOMPILE_FLAGS=--syntax-module LAMBDA

%/arithmetic-div-zero.lambda:
	true

include $(MAKEFILE_PATH)/../../../find-k.mak
include ${K_HOME}/include/ktest.mak

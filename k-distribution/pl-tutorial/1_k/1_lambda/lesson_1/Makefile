MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=lambda
EXT=lambda

%/arithmetic-div-zero.lambda:
	true

include $(MAKEFILE_PATH)/../../../find-k.mak
include ${K_HOME}/include/kframework/ktest.mak

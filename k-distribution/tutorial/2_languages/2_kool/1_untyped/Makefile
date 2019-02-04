MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=kool-untyped
EXT=kool
KOMPILE_FLAGS=-O2
KRUN_FLAGS=--output none

include $(MAKEFILE_PATH)/../../../find-k.mak
include ${K_HOME}/include/ktest.mak

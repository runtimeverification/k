MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=lambda
EXT=lambda
KOMPILE_FLAGS=--syntax-module LAMBDA --enable-search
KRUN_FLAGS=--search --pattern "<k> V:K </k>"

include $(MAKEFILE_PATH)/../../../find-k.mak
include ${K_HOME}/include/kframework/ktest.mak

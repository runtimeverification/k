MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=lambda
EXT=lambda
KOMPILE_FLAGS?=--syntax-module LAMBDA --backend java
KRUN_FLAGS?=--search --pattern "<k> V:K </k>"

include $(MAKEFILE_PATH)/../../../../include/ktest.mak

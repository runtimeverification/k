DEFDIR=$(abspath $(dir $(abspath $(firstword $(MAKEFILE_LIST))))/.. )
DEF=boundary-cells-test
EXT=a
KOMPILE_FLAGS=--syntax-module BOUNDARY-CELLS-TEST
KOMPILE_BACKEND?=java
KPROVE_FLAGS=--boundary-cells c1

TESTDIR=..
RESULTDIR=.

include ../../../../include/ktest.mak

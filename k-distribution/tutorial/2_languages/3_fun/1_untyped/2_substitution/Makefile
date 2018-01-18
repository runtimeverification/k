DEF=fun-untyped
EXT=fun
TESTDIR=../../programs
RESULTDIR=tests
KOMPILE_FLAGS=--backend java
KRUN_FLAGS=--pattern "<k> V:K </k>"

include ../../../../../include/ktest.mak

../../programs/calcc-looping.fun \
../../programs/references-5.fun \
../../programs/constructor-bst-sorting.fun \
../../programs/constructor-expr-distributivity.fun \
../../programs/factorial-and-list-max.fun \
../../programs/nth.fun \
../../programs/pattern.fun \
../../programs/references-1.fun \
../../programs/stuck-letrec.fun: kompile
	true

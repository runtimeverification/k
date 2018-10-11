#!/bin/sh

set -e
kompile --backend ocaml arith.k
krun ok.in | diff -u ok.out -
krun err.in | diff -u err.out -
rm -rf arith-kompiled

kompile --backend ocaml arith-threaded.k
krun ok.in | diff -u ok-threaded.out -
krun err.in | diff -u err-threaded.out -
rm -rf arith-threaded-kompiled



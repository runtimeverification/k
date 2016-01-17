#!/bin/bash

rm -rf *-kompiled
{ kompile b.k
  krun -cXA=1               1.b 2>&1 | diff - 1.b.out
  krun -cXA=1 -cXB=2        2.b 2>&1 | diff - 2.b.out
  krun -cXA=1 -cXB=2 -cXC=3 3.b 2>&1 | diff - 3.b.out
} >>x.k

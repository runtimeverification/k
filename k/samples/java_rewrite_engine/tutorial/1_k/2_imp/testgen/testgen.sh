#!/bin/bash
../../../../../../bin/kompile imp.k --backend java --test-gen -v
../../../../../../bin/krun --term while.imp --backend java --generate-tests --search -bound 100 -depth 300 --smt none --parens smart

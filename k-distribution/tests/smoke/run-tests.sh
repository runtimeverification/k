#!/usr/bin/env bash

# Run tests: bash run-tests.sh
# Update/generate output: CHECK=cp bash run-tests.sh

set -euxo pipefail

CHECK=(${CHECK:-git --no-pager diff --no-index --ignore-all-space -R})

echo "module TEST1 imports BOOL endmodule" > test1.k
kompile test1.k --backend haskell
rm -rf test1-kompiled

kompile test.k --main-module TEST --syntax-module TEST --backend llvm    --output-definition llvm-kompiled    --enable-search
kompile test.k --main-module TEST --syntax-module TEST --backend haskell --output-definition haskell-kompiled 

krun pgm1.test --definition llvm-kompiled > pgm1.test.out
"${CHECK[@]}" pgm1.test.out pgm1.test.expected

krun pgm2.test --definition llvm-kompiled > pgm2.test.out
"${CHECK[@]}" pgm2.test.out pgm2.test.expected

krun pgm1.test --definition llvm-kompiled --depth 1 --search > pgm2.test.search.out
"${CHECK[@]}" pgm2.test.search.out pgm2.test.search.expected

kprove test.k --spec-module TEST-SPEC --definition haskell-kompiled --claims TEST-SPEC.success
! kprove test.k --spec-module TEST-SPEC --definition haskell-kompiled --claims TEST-SPEC.failure

python3 <<HERE
import kllvm
sort_int = kllvm.ast.CompositeSort("SortInt")
assert str(sort_int) == "SortInt{}"
HERE

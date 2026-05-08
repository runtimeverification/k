SHELL=/bin/bash
# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ROOT=$(abspath $(MAKEFILE_PATH)/../..)
UV_RUN?=uv --project $(ROOT) run --
# path to builtin include directory
BUILTIN_DIR=$(abspath $(MAKEFILE_PATH)/../../../k-distribution/target/release/k/include/kframework/builtin)
# path to binary directory of this distribution
K_BIN=$(abspath $(MAKEFILE_PATH)/../../bin)
# path to the kompile binary of this distribuition
KOMPILE=$(UV_RUN) pyk kompile
# and krun
KRUN=$(UV_RUN) pyk krun
# and kdep
KDEP=$(UV_RUN) pyk kdep
# and kprove
KPROVE=$(UV_RUN) pyk kprove
# and kast
KAST=$(UV_RUN) pyk kast
# and kparse
KPARSE=$(UV_RUN) pyk kparse
# and kserver
KSERVER=$(UV_RUN) pyk kserver
# and ksearch
KSEARCH:=$(KRUN) --search-all
# and kprint
KPRINT=$(UV_RUN) pyk kprint
# and llvm-krun
LLVM_KRUN=$(UV_RUN) pyk llvm-krun
# and kdep
KDEP=$(UV_RUN) pyk kdep
# command to strip paths from test outputs
REMOVE_PATHS=| sed 's!\('`pwd`'\)/\(\./\)\{0,2\}!!g' | sed 's!\('${BUILTIN_DIR}'\)/\(\./\)\{0,2\}!!g' | sed 's!\('/nix/store/..*/include/kframework/builtin'\)/\(\./\)\{0,2\}!!g'

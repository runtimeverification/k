SHELL=/bin/bash
# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ROOT=$(abspath $(MAKEFILE_PATH)/../..)
UV_RUN?=uv --project $(ROOT) run --
# path to builtin include directory
BUILTIN_DIR=$(abspath $(shell dirname $(shell which kompile))/../include/kframework/builtin)
# path to binary directory of this distribution
K_BIN=$(abspath $(MAKEFILE_PATH)/../../bin)
# path to the kompile binary of this distribuition
KOMPILE=$(UV_RUN) pyk kompile
# and krun
KRUN=$(UV_RUN) pyk run
# and kdep
KDEP=${K_BIN}/kdep
# and kprove
KPROVE=$(UV_RUN) pyk prove
# and kast
KAST=$(UV_RUN) pyk parse
# and kparse
KPARSE=$(UV_RUN) pyk parse
# and kserver
KSERVER=$(UV_RUN) pyk kserver
# and ksearch
KSEARCH:=$(KRUN) --search-all
# and kprint
KPRINT=$(UV_RUN) pyk parse
# and llvm-krun
LLVM_KRUN=$(UV_RUN) pyk llvm-krun

# command to strip paths from test outputs
REMOVE_PATHS=| sed 's!\('`pwd`'\)/\(\./\)\{0,2\}!!g' | sed 's!\('${BUILTIN_DIR}'\)/\(\./\)\{0,2\}!!g' | sed 's!\('/nix/store/..*/include/kframework/builtin'\)/\(\./\)\{0,2\}!!g'

VERBOSITY?=

KOMPILE_FLAGS+=--no-exc-wrap --type-inference-mode checked $(VERBOSITY)
KPROVE_FLAGS+=--type-inference-mode checked --failure-info $(VERBOSITY)
KRUN_FLAGS+=$(VERBOSITY)
KAST_FLAGS+=$(VERBOSITY)

ifeq ($(UNAME), Darwin)
	KOMPILE_FLAGS+=--no-haskell-binary
endif

KRUN_OR_LEGACY=$(KRUN)

CHECK?=| diff -
CONSIDER_ERRORS=2>&1

PIPEFAIL?=set -o pipefail;
# null by default, add CONSIDER_PROVER_ERRORS=2>&1 to the local Makefile to test kprove output
#CONSIDER_PROVER_ERRORS=

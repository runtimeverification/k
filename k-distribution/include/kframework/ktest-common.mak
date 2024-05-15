SHELL=/bin/bash
# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to builtin include directory
BUILTIN_DIR=$(abspath $(MAKEFILE_PATH)/../../target/release/k/include/kframework/builtin)
# path to binary directory of this distribution
K_BIN=$(abspath $(MAKEFILE_PATH)/../../bin)
# path to the kompile binary of this distribuition
KOMPILE=${K_BIN}/kompile
# and krun
KRUN=${K_BIN}/krun
# and kdep
KDEP=${K_BIN}/kdep
# and kprove
KPROVE=${K_BIN}/kprove
# and kast
KAST=${K_BIN}/kast
# and kparse
KPARSE=${K_BIN}/kparse
# and kserver
KSERVER=${K_BIN}/kserver
# and ksearch
KSEARCH:=$(KRUN) --search-all
# and kprint
KPRINT=${K_BIN}/kprint
# and llvm-krun
LLVM_KRUN=${K_BIN}/llvm-krun
# and kdep
KDEP=${K_BIN}/kdep
# command to strip paths from test outputs
REMOVE_PATHS=| sed 's!\('`pwd`'\|'${BUILTIN_DIR}'\|/nix/store/.\+/include/kframework/builtin\)/\(\./\)\{0,2\}!!g'

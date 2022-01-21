DEF=test
EXT=test
TESTDIR=.
KRUN_FLAGS=--help
KOMPILE_FLAGS=--syntax-module TEST
PACKAGE_VERSION ?= $(shell cat ../../../../package/version)
GIT_MERGE_BASE=$(shell git merge-base HEAD master)
GIT_REVISION=$(shell git describe --contains --always ${GIT_MERGE_BASE} | sed 's/~.*//')
VERSION_REGEX="$(PACKAGE_VERSION)\|$(GIT_REVISION)"
KPARSE=${K_BIN}/kparse
KPARSE_GEN=${K_BIN}/kparse-gen
KORE_PRINT=${K_BIN}/kore-print

1.test:
	${KAST}       --help    | grep -q -- "--version"
	${KDEP}       --help    | grep -q -- "--version"
	${KEQ}        --help    | grep -q -- "--version"
	${KOMPILE}    --help    | grep -q -- "--version"
	${KPROVE}     --help    | grep -q -- "--version"
	${KRUN}       --help    | grep -q -- "--version"
	${KSERVER}    --help    | grep -q -- "--version"
	${KPARSE}     --help    | grep -q -- "--version"
	${KPARSE_GEN} --help    | grep -q -- "--version"
	${KORE_PRINT} --help    | grep -q -- "--version"
	${KAST}       --version | grep -q $(VERSION_REGEX)
	${KDEP}       --version | grep -q $(VERSION_REGEX)
	${KEQ}        --version | grep -q $(VERSION_REGEX)
	${KOMPILE}    --version | grep -q $(VERSION_REGEX)
	${KPROVE}     --version | grep -q $(VERSION_REGEX)
	${KRUN}       --version | grep -q $(VERSION_REGEX)
	${KSERVER}    --version | grep -q $(VERSION_REGEX)
	${KPARSE}     --version | grep -q $(VERSION_REGEX)
	${KPARSE_GEN} --version | grep -q $(VERSION_REGEX)
	${KORE_PRINT} --version | grep -q $(VERSION_REGEX)


include ../../../include/kframework/ktest.mak


DEF=test
EXT=test
TESTDIR=.
KRUN_FLAGS=--help
KOMPILE_FLAGS=--syntax-module TEST
PACKAGE_VERSION ?= $(shell cat ../../../../package/version)

1.test:
	${KAST}    --help    | grep -q -- "--version"
	${KDEP}    --help    | grep -q -- "--version"
	${KEQ}     --help    | grep -q -- "--version"
	${KOMPILE} --help    | grep -q -- "--version"
	${KPROVE}  --help    | grep -q -- "--version"
	${KRUN}    --help    | grep -q -- "--version"
	${KSERVER} --help    | grep -q -- "--version"
	${KAST}    --version | grep -q $(PACKAGE_VERSION)
	${KDEP}    --version | grep -q $(PACKAGE_VERSION)
	${KEQ}     --version | grep -q $(PACKAGE_VERSION)
	${KOMPILE} --version | grep -q $(PACKAGE_VERSION)
	${KPROVE}  --version | grep -q $(PACKAGE_VERSION)
	${KRUN}    --version | grep -q $(PACKAGE_VERSION)
	${KSERVER} --version | grep -q $(PACKAGE_VERSION)


include ../../../include/kframework/ktest.mak


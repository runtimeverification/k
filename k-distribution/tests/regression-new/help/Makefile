DEF=test
EXT=test
TESTDIR=.
KRUN_FLAGS=--help
KOMPILE_FLAGS=--syntax-module TEST

1.test:
	${KAST}    --help    | grep -q -- "--version"
	${KDEP}    --help    | grep -q -- "--version"
	${KEQ}     --help    | grep -q -- "--version"
	${KOMPILE} --help    | grep -q -- "--version"
	${KPROVE}  --help    | grep -q -- "--version"
	${KRUN}    --help    | grep -q -- "--version"
	${KSERVER} --help    | grep -q -- "--version"
	${KAST}    --version | grep -q $(shell cat ../../../../package/version)
	${KDEP}    --version | grep -q $(shell cat ../../../../package/version)
	${KEQ}     --version | grep -q $(shell cat ../../../../package/version)
	${KOMPILE} --version | grep -q $(shell cat ../../../../package/version)
	${KPROVE}  --version | grep -q $(shell cat ../../../../package/version)
	${KRUN}    --version | grep -q $(shell cat ../../../../package/version)
	${KSERVER} --version | grep -q $(shell cat ../../../../package/version)
	${KAST}    --version | grep -q $(shell cat ../../../../package/version.commit)
	${KDEP}    --version | grep -q $(shell cat ../../../../package/version.commit)
	${KEQ}     --version | grep -q $(shell cat ../../../../package/version.commit)
	${KOMPILE} --version | grep -q $(shell cat ../../../../package/version.commit)
	${KPROVE}  --version | grep -q $(shell cat ../../../../package/version.commit)
	${KRUN}    --version | grep -q $(shell cat ../../../../package/version.commit)
	${KSERVER} --version | grep -q $(shell cat ../../../../package/version.commit)


include ../../../include/kframework/ktest.mak


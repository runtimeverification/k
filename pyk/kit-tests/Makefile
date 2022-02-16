K_ROOT := $(abspath ../..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

export PATH := $(K_BIN):$(PATH)

KIT := kit


.PHONY: default clean test

default: test

clean:
	rm -rf .kit
	rm -rf .kprove-*

test:
	$(KIT) init --force verification.k looping-spec.k
	$(KIT) expand 3a8c..
	$(KIT) expand 3442..
	$(KIT) expand b528..
	$(KIT) expand 0678..
	$(KIT) cover  1846.. --by b528.. --semantic

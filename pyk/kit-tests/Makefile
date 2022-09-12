K_ROOT := $(abspath ../..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

export PATH := $(K_BIN):$(PATH)

CHECK = git --no-pager diff --no-index -R

.PHONY: all clean update-results test  kit-tests test-kit

all: test

clean:
	rm -rf definitions
	$(MAKE) -C post-process clean

update-results: CHECK=cp
update-results: test


# Tests
# =====

test: test-kit

# kpyk runner tests
# -----------------

TEST_KIT := ./test-kit.sh

%.test.run: %.test %-spec.k
	$(TEST_KIT) $< > $@.out
	$(CHECK) $@.out $@.expected

kit_tests:= $(wildcard ./*/*.test)

test-kit: $(kit_tests:=.run)

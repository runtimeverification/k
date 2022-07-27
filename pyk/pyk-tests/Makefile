K_ROOT := $(abspath ../..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

KOMPILE = $(K_BIN)/kompile
PYK     = pyk

export PATH := $(K_BIN):$(PATH)

CHECK = git --no-pager diff --no-index -R


.PHONY: all clean update-results \
        test test-kpyk test-kpyk-graphviz test-kpyk-minimize-term test-post-process

all: test

clean:
	rm -rf definitions
	$(MAKE) -C post-process clean

update-results: CHECK=cp
update-results: test


# Tests

test: test-kpyk

## kpyk runner tests

test-kpyk: test-kpyk-graphviz test-kpyk-minimize-term test-post-process

test-kpyk-graphviz: d.kompiled
	$(PYK) -v definitions/d graph-imports
	cat definitions/d/import-graph | tr -cd '[:alnum:]\n' | grep . | tr '[:lower:]' '[:upper:]' | grep -xFf import-graph.expected | sort > import-graph.out
	$(CHECK) import-graph.out import-graph.expected

test-kpyk-minimize-term: imp-verification.kompiled
	$(PYK) -v definitions/imp-verification prove ../k-files/imp-verification.k ../k-files/imp-unproveable-spec.k IMP-UNPROVEABLE-SPEC \
	    | $(PYK) -v definitions/imp-verification print /dev/stdin > imp-unproveable-spec.k.out
	$(CHECK) imp-unproveable-spec.k.out imp-unproveable-spec.k.expected

test-post-process:
	$(MAKE) -C post-process


## definitions to build ahead of time

definitions := imp-verification

build-definitions: $(definitions:=.kompiled)

%.kompiled:
	$(KOMPILE) ../k-files/$*.k             \
	    --output-definition definitions/$* \
	    --backend haskell                  \
	    --emit-json

# find K_HOME
include ../find-k.mak
K_BIN=$(abspath ${K_HOME}/bin)

# used programs
KOMPILE=$(K_BIN)/kompile
BOOSTER=$(K_BIN)/kore-rpc-booster
RPC_CLIENT=$(K_BIN)/kore-rpc-client

# tests
INPUTS=$(wildcard *-request.json)
TESTS=$(INPUTS:-request.json=.rpc)

.phony: clean all update-results $(TESTS)

all: $(TESTS)

update-results: $(TESTS:.rpc=.update)

####################
KOMPILED_DIR=imp-kompiled
kompile: $(KOMPILED_DIR)/definition.kore

$(KOMPILED_DIR)/definition.kore: ../imp.k
	$(KOMPILE) --backend haskell --output-definition $(KOMPILED_DIR) $<

####################
KOMPILED_LLVM_DIR=imp-llvm-kompiled
ifeq ($(shell uname -s),Darwin)
	LIB_SUFFIX=dylib
else
	LIB_SUFFIX=so
endif

kompile-llvm: $(KOMPILED_LLVM_DIR)/interpreter.$(LIB_SUFFIX)

$(KOMPILED_LLVM_DIR)/interpreter.$(LIB_SUFFIX): ../imp.k
	$(KOMPILE) --backend llvm --llvm-kompile-type c --output-definition $(KOMPILED_LLVM_DIR) $<

clean:
	rm -rf $(KOMPILED_DIR) $(KOMPILED_LLVM_DIR)

####################
$(TESTS): %.rpc: %-request.json %-response.json kompile kompile-llvm
	($(BOOSTER) \
		$(KOMPILED_DIR)/definition.kore --module IMP \
		--llvm-backend-library ./$(KOMPILED_LLVM_DIR)/interpreter.$(LIB_SUFFIX) & \
		echo $$! > server.pid\
	)
	@echo "Server running as process $$(cat server.pid)"
	bash -c "trap 'kill -2 $$(cat server.pid); rm server.pid' ERR EXIT; $(RPC_CLIENT) send $*-request.json --expect $*-response.json $(REGENERATE)"

$(TESTS:.rpc=.update): %.update:
	$(MAKE) $*.rpc REGENERATE="--regenerate"

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
		$(KOMPILED_DIR)/definition.kore --module IMP --server-port 0 \
		--llvm-backend-library ./$(KOMPILED_LLVM_DIR)/interpreter.$(LIB_SUFFIX) & \
		echo $$! > $*.server.pid)
	bash -c "while ! lsof -a -p$$(cat $*.server.pid) -sTCP:LISTEN -iTCP; do echo .; sleep 1; done"
	lsof -a -p$$(cat $*.server.pid) -sTCP:LISTEN -iTCP | grep $$(cat $*.server.pid) | sed -e 's/.* TCP \*:\([0-9]*\).*$$/\1/' > $*.server.port

	@echo "Server running as process $$(cat $*.server.pid) on port $$(cat $*.server.port)"
	bash -c "trap 'kill -2 $$(cat $*.server.pid); rm $*.server.{pid,port}' EXIT; $(RPC_CLIENT) --port $$(cat $*.server.port) send $*-request.json --expect $*-response.json $(REGENERATE)"

$(TESTS:.rpc=.update): %.update:
	$(MAKE) $*.rpc REGENERATE="--regenerate"

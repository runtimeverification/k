# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kompile binary of this distribuition
K_BIN=$(abspath $(MAKEFILE_PATH)/../../bin)
KOMPILE=${K_BIN}/kompile
KOMPILE_BACKEND=java
# ditto for keq
KEQ=${K_BIN}/keq

BASIC_SMT=$(abspath $(MAKEFILE_PATH)/z3/basic.smt2)

CHECK=| diff -

.PHONY: kompile keq all clean krun proofs bmc searches strat kast

all: kompile keq

kompile: $(DEF1)/$(DEF1)-kompiled/timestamp $(DEF2)/$(DEF2)-kompiled/timestamp $(DEF0)/$(DEF0)-kompiled/timestamp

$(DEF0)/$(DEF0)-kompiled/timestamp: $(DEF0).k
	$(KOMPILE) $(DEBUG) $< -d $(DEF0) --backend $(KOMPILE_BACKEND)
$(DEF1)/$(DEF1)-kompiled/timestamp: $(DEF1).k
	$(KOMPILE) $(DEBUG) $< -d $(DEF1) --backend $(KOMPILE_BACKEND)
$(DEF2)/$(DEF2)-kompiled/timestamp: $(DEF2).k
	$(KOMPILE) $(DEBUG) $< -d $(DEF2) --backend $(KOMPILE_BACKEND)

keq: $(SPEC1) $(SPEC2) kompile
	$(KEQ) $(DEBUG) -d $(DEF0) -d1 $(DEF1) -d2 $(DEF2) -s1 $(SPEC1) -s2 $(SPEC2) -sm1 $(MODULE1) -sm2 $(MODULE2) --smt_prelude $(BASIC_SMT)

clean:
	rm -rf $(DEF0) $(DEF1) $(DEF2)

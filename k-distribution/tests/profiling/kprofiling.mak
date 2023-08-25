# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to binary directory of this distribution
K_BIN=$(abspath $(MAKEFILE_PATH)/../../bin)
# path to the kompile binary of this distribuition
KOMPILE=${K_BIN}/kompile
# time command for profiling kompile
TIME=/usr/bin/time
PROFILING_RESULTS=.profiling-results.json
# check if .k file exists, if not, check if .md file exists
# if not, default to .k to give error message
SOURCE_EXT?=$(or $(and $(wildcard $(DEF).k), k), $(or $(and $(wildcard $(DEF).md), md), k))
# path to put -kompiled directory in
DEFDIR?=.
# path to kompile output directory
KOMPILED_DIR=$(DEFDIR)/$(notdir $(DEF))-kompiled

# profiles the kompile step
profile: clean
	$(TIME) --format "{\n\t\"$(BENCHMARK_NAME)\": {\n\t\t\"build-time\": {\n\t\t\t\"value\": %e\n\t\t},\n\t\t\"max-resident-set-size\": {\n\t\t\t\"value\": %M\n\t\t}\n\t}\n}" --output=$(PROFILING_RESULTS) $(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $(DEF).$(SOURCE_EXT) --output-definition $(KOMPILED_DIR)

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz .profiling-results.json
ifeq ($(KOMPILE_BACKEND),kore)
	rm -f $(DEF).kore
endif
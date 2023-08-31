# path to the kompile binary of this distribuition
KOMPILE?=$(shell which kompile)
# time command for profiling kompile
ifeq ($(shell uname -s),Darwin)
	TIME?=$(shell which gtime)
else
	TIME?=/usr/bin/time
endif
PROFILING_RESULTS=.profiling-results.json
# check if .k file exists, if not, check if .md file exists
# if not, default to .k to give error message
SOURCE_EXT?=$(or $(and $(wildcard $(DEF).k), k), $(or $(and $(wildcard $(DEF).md), md), k))
# path to put -kompiled directory in
DEFDIR?=.
# path to kompile output directory
KOMPILED_DIR=$(DEFDIR)/$(notdir $(DEF))-kompiled

# Bencher command
BENCHER_RUN=bencher run
# Bencher flags
BENCHER_RUN_BRANCH_ARGS=--if-branch "${GITHUB_HEAD_REF}" --else-if-branch "${GITHUB_BASE_REF}" --else-if-branch master
BENCHER_RUN_CI_ARGS=--err --iter ${ITER} --fold mean --ci-only-on-alert --github-actions "${GITHUB_TOKEN}" --file $(PROFILING_RESULTS)

# As Bencher v0.3.9 consume all output from the command, we need to use this
# workaround to print the verbose output ok kompile, we also have to use this to
# print any errors or warnings.
VERBOSE_WORKAROUND_GET=> verbose.out 2> warn_errs.out
VERBOSE_WORKAROUND_CAT=&& cat verbose.out && cat warn_errs.out && rm verbose.out warn_errs.out

# JSON format for Bencher input
JSON_FORMAT="{\n\t\"$(BENCHMARK_NAME)\": {\n\t\t\"build-time\": {\n\t\t\t\"value\": %e\n\t\t},\n\t\t\"max-resident-set-size\": {\n\t\t\t\"value\": %M\n\t\t}\n\t}\n}"

# profiles the kompile step
profile: clean
	$(BENCHER_RUN) $(BENCHER_RUN_BRANCH_ARGS) $(BENCHER_RUN_CI_ARGS) 		   \
		'$(TIME) --format ${JSON_FORMAT} --output=$(PROFILING_RESULTS) 		   \
			$(KOMPILE) -v $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $(DEF).$(SOURCE_EXT) --output-definition $(KOMPILED_DIR) $(VERBOSE_WORKAROUND_GET)' \
			$(VERBOSE_WORKAROUND_CAT)

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz .profiling-results.json
ifeq ($(KOMPILE_BACKEND),kore)
	rm -f $(DEF).kore
endif

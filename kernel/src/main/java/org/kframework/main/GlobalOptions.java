// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.main;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.options.BaseEnumConverter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

public final class GlobalOptions {

    public GlobalOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public GlobalOptions(Void v) {}

    public GlobalOptions(boolean debug, Warnings warnings, boolean verbose) {
        this.debug = debug;
        this.warnings = warnings;
        this.verbose = verbose;
    }

    public GlobalOptions(boolean debug, Warnings warnings, boolean verbose, boolean warnings2errors) {
        this.debug = debug;
        this.warnings = warnings;
        this.verbose = verbose;
        this.warnings2errors = warnings2errors;
    }

    public static enum Warnings {
        /**
         * All warnings and errors
         */
        ALL(EnumSet.allOf(ExceptionType.class)),

        /**
         * All warnings and errors except hidden warnings
         */
        NORMAL(EnumSet.complementOf(EnumSet.of(ExceptionType.HIDDENWARNING))),

        /**
         * No warnings, only errors
         */
        NONE(EnumSet.of(ExceptionType.ERROR));

        private Warnings(Set<ExceptionType> types) {
            typesIncluded = types;
        }
        private Set<ExceptionType> typesIncluded;

        public boolean includesExceptionType(ExceptionType e) {
            return typesIncluded.contains(e);
        }
    }

    public static class WarningsConverter extends BaseEnumConverter<Warnings> {

        public WarningsConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<Warnings> enumClass() {
            return Warnings.class;
        }
    }

    @Parameter(names={"--help", "-h"}, description="Print this help message", help = true)
    public boolean help = false;

    @Parameter(names={"--help-experimental", "-X"}, description="Print help on non-standard options.", help=true)
    public boolean helpExperimental = false;

    @Parameter(names="--version", description="Print version information")
    public boolean version = false;

    @Parameter(names={"--verbose", "-v"}, description="Print verbose output messages")
    public boolean verbose = false;

    @Parameter(names="--debug", description="Print debugging output messages")
    public boolean debug = false;

    @Parameter(names = "--debug-steps", variableArity = true, description = "Specify exact steps for which --debug option should be enabled")
    public List<String> debugSteps = new ArrayList<>();

    @Parameter(names={"--warnings", "-w"}, converter=WarningsConverter.class, description="Warning level. Values: [all|normal|none]")
    public Warnings warnings = Warnings.NORMAL;

    @Parameter(names={"--warnings-to-errors", "-w2e"}, description="Convert warnings to errors.")
    public boolean warnings2errors = false;

    @Parameter(names="--log-cells", description="Specify what subset of configuration has to be printed when" +
            " an execution step is logged." +
            " Usage format: --log-pretty \"v2,v2,...\" , where v1,v2,... are either cell names," +
            " cell names in parentheses (like \"(k)\") or one of: \"(#pc)\", \"(#result)\". " +
            " The cells specified without parentheses are printed with toString()." +
            " The cells specified in parentheses are pretty-printed. Certain cells have custom formatting." +
            " The last 2 options mean:" +
            " (#pc) = pretty print the path condition (constraint)." +
            " (#result) = fully pretty-print the final result (e.g. the configuration for paths that were not proved)." +
            " This last option is very slow." +
            " Default value is:" +
            " --log-cells k,output,statusCode,localMem,pc,gas,wordStack,callData,accounts" +
            " Recommended alternative value:" +
            " --log-cells \"(k),output,statusCode,localMem,pc,gas,wordStack,callData,accounts,(#pc)\"")
    public List<String> logCells = Arrays.asList("k", "output", "statusCode", "localMem", "pc", "gas", "wordStack",
            "callData", "accounts");

    @Parameter(names="--branching-allowed", arity=1, description="Number of branching events allowed before a forcible stop.")
    public int branchingAllowed = Integer.MAX_VALUE;

    @Parameter(names="--log", description="Log every step.")
    public boolean log = false;

    @Parameter(names = "--debug-last-step", description = "Activate option --debug for last step. Useful to debug final implication.")
    public boolean debugLastStep = false;

    @Parameter(names="--debug-spec-rules", description="Enable --debug for steps where a specification rule is applied. " +
            "This may be useful because during spec rules new constraints are sometimes added to the path condition.")
    public boolean debugSpecRules = false;

    @Parameter(names="--log-rules", description="Log applied rules.")
    public boolean logRules = false;

    @Parameter(names="--log-target", description="Log target term.")
    public boolean logTarget = false;

    @Parameter(names="--log-stmts-only", description="Log only steps that execute a statement, without intermediary steps. " +
            "Except when intermediary steps are important for other reason, like branching.")
    public boolean logStmtsOnly = false;

    @Parameter(names="--log-basic",
            description="Log most basic information: summary of initial step, final steps and final implications." +
                    " All custom logging only works for KEVM-based specs.")
    public boolean logBasic = false;

    @Parameter(names="--debug-z3",
            description="Log formulae fed to z3 together with the rule that triggered them.")
    public boolean debugZ3 = false;

    @Parameter(names="--debug-z3-queries",
            description="Log actual z3 queries. Activates --debug-z3 automatically.")
    public boolean debugZ3Queries = false;

    @Parameter(names="--cache-func",
            description="Cache evaluation results of pure functions. Only for kprove.", arity = 1)
    public boolean cacheFunctions = true;

    @Parameter(names="--cache-tostring",
            description="Cache toString() result for KItem, Equality and DisjunctiveFormula. " +
                    "Speeds up logging but eats more memory.", arity = 1)
    public boolean cacheToString = true;

    @Parameter(names = "--log-memory-after-gc",
            description = "In the summary box, in addition to printing regular used memory, " +
                    "also print used memory after System.gc(). Gives more precise information about memory usage.")
    public boolean logMemoryAfterGC = false;

    @Parameter(names = "--log-success", description = "Log success final states. " +
            "By default only failure final states are logged.")
    public boolean logSuccessFinalStates = false;

    public boolean logRulesPublic = false;
}

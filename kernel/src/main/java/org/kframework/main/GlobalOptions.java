// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.main;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.options.BaseEnumConverter;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

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

    @Parameter(names="--fast", description="Print final configs with toString() rather than pretty print.")
    public boolean fast = false;

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

    @Parameter(names="--log-stmts-only", description="Log only steps that execute a statement, without intermediary steps. " +
            "Except when intermediary steps are important for other reason, like branching.")
    public boolean logStmtsOnly = false;

    @Parameter(names="--log-basic",
            description="Log most basic information: summary of initial step, final steps and final implications." +
                    " All custom logging only works for KEVM-based specs.")
    public boolean logBasic = false;

    public boolean logRulesPublic = false;
}

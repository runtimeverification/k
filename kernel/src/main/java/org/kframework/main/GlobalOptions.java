// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.main;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.DurationConverter;

import java.time.Duration;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public final class GlobalOptions {

    public GlobalOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    /**
     * Prevents instantiation by Guice when not explicitly configured in a Module.
     */
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
        NORMAL(EnumSet.range(ExceptionType.ERROR, ExceptionType.FIRST_HIDDEN)),

        /**
         * No warnings, only errors
         */
        NONE(EnumSet.of(ExceptionType.ERROR));

        private Warnings(Set<ExceptionType> types) {
            typesIncluded = types;
        }
        private Set<ExceptionType> typesIncluded;

        public Set<ExceptionType> getTypesIncluded() { return typesIncluded; }
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

    public static class ExceptionTypeConverter extends BaseEnumConverter<ExceptionType> {

        public ExceptionTypeConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<ExceptionType> enumClass() {
            return ExceptionType.class;
        }
    }

    private Set<ExceptionType> typesIncluded;

    public boolean includesExceptionType(ExceptionType e) {
        Set<ExceptionType> t = typesIncluded;
        if (t == null) {
            t = new HashSet<>(warnings.getTypesIncluded());
            t.addAll(enableWarnings);
            t.removeAll(disableWarnings);
            if (!t.contains(ExceptionType.ERROR)) {
                throw KEMException.criticalError("Cannot disable errors with -Wno.");
            }
            typesIncluded = t;
        }
        return t.contains(e);
    }

    @Parameter(names={"--help", "-h"}, description="Print this help message", help = true)
    public boolean help = false;

    @Parameter(names="--version", description="Print version information")
    public boolean version = false;

    @Parameter(names={"--verbose", "-v"}, description="Print verbose output messages")
    public boolean verbose = false;

    @Parameter(names="--debug", description="Print debugging output messages and error stack traces")
    private boolean debug = false;

    @Parameter(names="--debug-warnings", description="Print debugging output messages and error/warning stack traces")
    public boolean debugWarnings = false;

    @Parameter(names={"--warnings", "-w"}, converter=WarningsConverter.class, description="Warning level. Values: [all|normal|none]")
    public Warnings warnings = Warnings.NORMAL;

    @Parameter(names="-W", description="Enable specific warning categories. Values: [non-exhaustive-match|undeleted-temp-dir|missing-hook-ocaml|missing-hook-java|missing-syntax-module|invalid-exit-code|deprecated-backend|invalid-config-var|future-error|unused-var|proof-lint|useless-rule|unresolved-function-symbol|malformed-markdown|invalidated-cache|unused-symbol]", converter=ExceptionTypeConverter.class)
    public List<ExceptionType> enableWarnings = Collections.emptyList();

    @Parameter(names="-Wno", description="Disable specific warning categories.", converter=ExceptionTypeConverter.class)
    public List<ExceptionType> disableWarnings = Collections.emptyList();

    @Parameter(names={"--warnings-to-errors", "-w2e"}, description="Convert warnings to errors.")
    public boolean warnings2errors = false;

    @Parameter(names="--profile-rule-parsing", description="Generate time in seconds to parse each rule in the semantics.")
    public String profileRules;

    @Parameter(names = {"--shutdown-wait-time"}, converter = DurationConverter.class,
            description = "If option is set, a shutdown hook will be registered " +
                    "that, once invoked, interrupts the main thread and waits its termination. " +
                    "The wait time is the argument of this option, in format like 10ms/10s/10m/10h. " +
                    "Useful if K is interrupted by Ctrl+C, because it allows the backend to detect " +
                    "interruption and print diagnostics information. Currently interruption detection is implemented " +
                    "in Java Backend. If K is invoked from KServer (e.g. Nailgun), the option is ignored.")
    public Duration shutdownWaitTime;

    @Parameter(names = {"--timeout"}, converter = DurationConverter.class,
            description = "If option is set, timeout for this process, in format like 10ms/10s/10m/10h. " +
                    "Using this option is preferred compared to bash timeout command, which has known limitations " +
                    "when invoked from scripts.")
    public Duration timeout;

    @Parameter(names={"--no-exc-wrap"}, description="Do not wrap exception messages to 80 chars. Keep long lines.")
    public boolean noExcWrap = false;

    public boolean debug() {
        return debug || debugWarnings;
    }
}

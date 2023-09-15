// Copyright (c) K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

import java.io.Serializable;

public class SMTOptions implements Serializable {

    public SMTOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public SMTOptions(Void v) {}

    @Parameter(names="--smt", descriptionKey = "executable", converter=SMTSolverConverter.class,
            description="SMT solver to use for checking constraints. <executable> is one of [z3|none].", hidden = true)
    public SMTSolver smt = SMTSolver.Z3;

    public static class SMTSolverConverter extends BaseEnumConverter<SMTSolver> {

        public SMTSolverConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<SMTSolver> enumClass() {
            return SMTSolver.class;
        }
    }

    @Parameter(names="--ignore-missing-smtlib-warning",
            description="Suppress warning when SMTLib translation fails.", hidden = true)
    public boolean ignoreMissingSMTLibWarning = false;

    @Parameter(names="--floats-as-po",
            description="Abstracts floating-point values as a partial order relation.", hidden = true)
    public boolean floatsAsPO = false;

    @Parameter(names="--maps-as-int-array", description="Abstracts map values as an array of ints.", hidden = true)
    public boolean mapAsIntArray = false;

    @Parameter(names={"--smt-prelude", "--smt_prelude"},
            description="Path to the SMT prelude file.", descriptionKey = "path", hidden = true)
    public String smtPrelude;

    @Parameter(names="--smt-timeout", descriptionKey = "milliseconds",
            description="Timeout for calls to the SMT solver, in milliseconds.", hidden = true)
    public Integer smtTimeout = null;

    @Parameter(names="--z3-jni", description="Invokes Z3 as JNI library. Default is external process. " +
            "JNI is slightly faster, but can potentially lead to JVM crash.", hidden = true)
    public boolean z3JNI = false;

    @Parameter(names="--z3-tactic", descriptionKey = "solver",
            description="The path to solver tactic to use to check satisfiability in Z3.", hidden = true)
    public String z3Tactic;
}

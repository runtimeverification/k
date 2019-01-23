// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

import java.io.Serializable;

public class SMTOptions implements Serializable {

    public SMTOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public SMTOptions(Void v) {}

    @Parameter(names="--smt", converter=SMTSolverConverter.class, description="SMT solver to use for checking constraints. <solver> is one of [z3|none].")
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

    @Parameter(names="--ignore-missing-smtlib-warning", description="Suppress warning when SMTLib translation fails.")
    public boolean ignoreMissingSMTLibWarning = false;

    @Parameter(names="--floats-as-po", description="Abstracts floating-point values as a partial order relation.")
    public boolean floatsAsPO = false;

    @Parameter(names="--maps-as-int-array", description="Abstracts map values as an array of ints.")
    public boolean mapAsIntArray = false;

    @Parameter(names={"--smt-prelude", "--smt_prelude"}, description="Path to the SMT prelude file.")
    public String smtPrelude;

    @Parameter(names="--z3-jni", description="Invokes Z3 as JNI library. Default is external process. " +
            "JNI is slightly faster, but can potentially lead to JVM crash.")
    public boolean z3JNI = false;

    @Parameter(names="--z3-cnstr-timeout", description="The default soft timeout (in milli seconds) of Z3 for checking constraint satisfiability.")
    public int z3CnstrTimeout = 50;

    @Parameter(names="--z3-impl-timeout", description="The default soft timeout (in milli seconds) of Z3 for checking implication.")
    public int z3ImplTimeout = 5000;

    @Parameter(names="--z3-tactic", description="The solver tactic to use to check satisfiability in Z3.")
    public String z3Tactic;
}

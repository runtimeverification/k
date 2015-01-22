// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.options;

import java.io.Serializable;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

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

    @Parameter(names="--smt_prelude", description="Path to the SMT prelude file.")
    public String smtPrelude;

    @Parameter(names="--z3-executable", description="Invokes Z3 as an external process.")
    public boolean z3Executable = false;

    @Parameter(names="--z3-cnstr-timeout", description="The default soft timeout (in milli seconds) of Z3 for checking constraint satisfiability.")
    public int z3CnstrTimeout = 50;

    @Parameter(names="--z3-impl-timeout", description="The default soft timeout (in milli seconds) of Z3 for checking implication.")
    public int z3ImplTimeout = 5000;
}

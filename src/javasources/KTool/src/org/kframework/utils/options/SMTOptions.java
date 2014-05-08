// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import java.io.Serializable;

import com.beust.jcommander.Parameter;

public class SMTOptions implements Serializable {

    @Parameter(names="--smt", converter=SMTSolverConverter.class, description="SMT solver to use for checking constraints. <solver> is one of [z3|gappa|none].")
    public SMTSolver smt = SMTSolver.Z3;
    
    public static class SMTSolverConverter extends BaseEnumConverter<SMTSolver> {

        @Override
        public Class<SMTSolver> enumClass() {
            return SMTSolver.class;
        }
    }
}

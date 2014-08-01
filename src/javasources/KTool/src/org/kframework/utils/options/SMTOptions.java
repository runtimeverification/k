// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import java.io.Serializable;

import org.kframework.utils.inject.NullProvider;

import com.beust.jcommander.Parameter;
import com.google.inject.ProvidedBy;

@ProvidedBy(NullProvider.class)
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

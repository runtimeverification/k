// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import java.io.Serializable;

public class SMTOptions implements Serializable {

  public SMTOptions() {}

  @Parameter(
      names = "--smt",
      converter = SMTSolverConverter.class,
      description = "SMT solver to use for checking constraints. <executable> is one of [z3|none].",
      descriptionKey = "executable",
      hidden = true)
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

  @Parameter(
      names = {"--smt-prelude", "--smt_prelude"},
      description = "Path to the SMT prelude file.",
      descriptionKey = "path",
      hidden = true)
  public String smtPrelude;

  @Parameter(
      names = "--smt-timeout",
      descriptionKey = "milliseconds",
      description = "Timeout for calls to the SMT solver, in milliseconds.",
      hidden = true)
  public Integer smtTimeout = null;
}

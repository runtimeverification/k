// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public final class JavaExecutionOptions {

    @Parameter(names="--deterministic-functions", description="Throw assertion failure during "
        + "execution in the java backend if function definitions are not deterministic.")
    public boolean deterministicFunctions = false;

    @Parameter(names="--symbolic-execution", description="Use unification rather than "
        + "pattern matching to drive rewriting in the Java backend.")
    public boolean symbolicExecution = false;

    @Parameter(names="--audit-file", description="Enforce that the rule applied at the step specified by "
            + "--apply-step is a rule at the specified file and line, or fail with an error explaining why "
            + "the rule did not apply.")
    public String auditingFile;

    @Parameter(names="--audit-line", description="Enforce that the rule applied at the step specified by "
            + "--apply-step is a rule at the specified file and line, or fail with an error explaining why "
            + "the rule did not apply.")
    public Integer auditingLine;

    @Parameter(names="--audit-step", description="Enforce that the rule applied at the specified step is a rule "
            + "tagged with the javaBackendValue of --apply-tag, or fail with an error explaining why the rule did not apply.")
    public Integer auditingStep;

    @Parameter(names = "--log-subst", description = "When a ConjunctiveFormula is logged, also log substitutions. " +
            "Used in combination with --debug-z3.")
    public boolean logSubst = false;

    @Parameter(names = "--log-implication-lhs", description = "When a ConjunctiveFormula for implication is logged, " +
            "log both LHS and RHS. This is the default behavior. If this option is false, only RHS will be logged, " +
            "to reduce lgo size. Used in combination with --debug-z3.", arity = 1)
    public boolean logImplicationLHS = true;
}

// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Provider;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.FormulaContext;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.utils.IndentingFormatter;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.SMTSolver;

import java.util.Set;

public class SMTOperations {

    private final SMTOptions        smtOptions;
    private final Z3Wrapper         z3;
    private final JavaExecutionOptions javaExecutionOptions;
    private final KExceptionManager kem;

    public SMTOperations(
            Provider<Definition> definitionProvider,
            SMTOptions smtOptions,
            Z3Wrapper z3,
            KExceptionManager kem,
            JavaExecutionOptions javaExecutionOptions) {
        this.smtOptions = smtOptions;
        this.z3         = z3;
        this.kem        = kem;
        this.javaExecutionOptions = javaExecutionOptions;
    }

    public boolean checkUnsat(ConjunctiveFormula constraint, FormulaContext formulaContext) {
        if (smtOptions.smt != SMTSolver.Z3) {
            return false;
        }

        if (constraint.isSubstitution()) {
            return false;
        }

        IndentingFormatter log = constraint.globalContext().log();
        boolean result = false;
        try {
            constraint.globalContext().profiler.queryBuildTimer.start();
            CharSequence query;
            if (javaExecutionOptions.debugZ3Queries) {
                log.format("\nAnonymous vars in query:\n");
            }
            try {
                query = KILtoSMTLib.translateConstraint(constraint).toString();
            } finally {
                constraint.globalContext().profiler.queryBuildTimer.stop();
            }
            if (javaExecutionOptions.debugZ3Queries) {
                log.format("\nZ3 constraint query:\n%s\n", query);
            }
            result = z3.isUnsat(query, smtOptions.z3CnstrTimeout, formulaContext.z3Profiler);
            if (result && RuleAuditing.isAuditBegun()) {
                log.format("SMT query returned unsat: %s\n", query);
            }
        } catch (UnsupportedOperationException e) {
            e.printStackTrace();
            kem.registerCriticalWarning(ExceptionType.PROOF_LINT, "z3 constraint query: " + e.getMessage(), e);
            if (javaExecutionOptions.debugZ3) {
                log.format("\nZ3 constraint warning: %s\n", e.getMessage());
            }
            formulaContext.z3Profiler.newQueryBuildFailure();
        } catch (KEMException e) {
            e.exception.formatTraceFrame("\nwhile checking satisfiability for:\n%s", constraint.toStringMultiline());
            throw e;
        }
        return result;
    }

    /**
     * Checks if {@code left => right}, or {@code left /\ !right} is unsat.
     * Assuming that {@code existentialQuantVars} are existentially quantified.
     */
    public boolean impliesSMT(
            ConjunctiveFormula left,
            ConjunctiveFormula right,
            Set<Variable> existentialQuantVars, FormulaContext formulaContext) {
        if (smtOptions.smt == SMTSolver.Z3) {
            IndentingFormatter log = left.globalContext().log();
            try {
                left.globalContext().profiler.queryBuildTimer.start();
                CharSequence query;
                if (javaExecutionOptions.debugZ3Queries) {
                    log.format("\nAnonymous vars in query:\n");
                }
                try {
                    query = KILtoSMTLib.translateImplication(left, right, existentialQuantVars).toString();
                } finally {
                    left.globalContext().profiler.queryBuildTimer.stop();
                }
                if (javaExecutionOptions.debugZ3Queries) {
                    log.format("\nZ3 query:\n%s\n", query);
                }
                return z3.isUnsat(query, smtOptions.z3ImplTimeout, formulaContext.z3Profiler);
            } catch (UnsupportedOperationException | SMTTranslationFailure e) {
                if (!smtOptions.ignoreMissingSMTLibWarning) {
                    //These warnings have different degree of relevance depending whether they are in init or execution phase
                    String warnPrefix = left.globalContext().isExecutionPhase() ? "execution phase: " : "init phase: ";
                    String warnMsg = warnPrefix + e.getMessage() + " .";
                    if (!javaExecutionOptions.debugZ3) {
                        warnMsg += " Please re-run with the --debug-z3 flag.";
                    }
                    warnMsg += " Search the logs starting with 'Z3 warning' to see the Z3 implication " +
                            "that generated the warning.";
                    kem.registerInternalWarning(ExceptionType.PROOF_LINT, warnMsg, e);
                }
                if (javaExecutionOptions.debugZ3) {
                    log.format("\nZ3 warning. Query not generated: %s\n", e.getMessage());
                }
                formulaContext.queryBuildFailure();
            } catch (KEMException e) {
                e.exception.formatTraceFrame("\nwhile proving implication LHS:\n%s\nRHS:\n%s",
                        left.toStringMultiline(), right.toStringMultiline());
                throw e;
            }
        }
        return false;
    }
}

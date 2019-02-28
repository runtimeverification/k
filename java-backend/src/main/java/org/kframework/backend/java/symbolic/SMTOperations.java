// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Provider;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.FormulaContext;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.builtin.Sorts;
import org.kframework.kore.KORE;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.SMTSolver;

import com.google.common.collect.ImmutableSet;
import com.google.inject.Provider;

import java.util.Set;

public class SMTOperations {

    public static final ImmutableSet<Sort> SMTLIB_BUILTIN_SORTS = ImmutableSet.of(
            Sort.BOOL,
            Sort.INT,
            Sort.BIT_VECTOR,
            Sort.of(Sorts.Float()),
            Sort.of(Sorts.String()),
            Sort.of(KORE.Sort("IntSet")),
            Sort.of(KORE.Sort("MIntSet")),
            Sort.of(KORE.Sort("FloatSet")),
            Sort.of(KORE.Sort("StringSet")),
            Sort.of(KORE.Sort("IntSeq")),
            Sort.of(KORE.Sort("MIntSeq")),
            Sort.of(KORE.Sort("FloatSeq")),
            Sort.of(KORE.Sort("StringSeq")));
    public static final ImmutableSet<String> SMTLIB_BUILTIN_FUNCTIONS = ImmutableSet.of(
            "forall",
            "exists",
            /* array theory */
            "select",
            "store",
            /* core theory */
            "not",
            "and",
            "or",
            "xor",
            "=>",
            "=",
            "distinct",
            "ite",
            /* int theory */
            "+",
            "-",
            "*",
            "div",
            "mod",
            "abs",
            "<=",
            "<",
            ">=",
            ">",
            "^",
            /* extra int theory */
            "int_max",
            "int_min",
            "int_abs",
            /* extra float theory */
            "remainder",
            "min",
            "max",
            "==",
            /* bit vector theory */
            "concat",
            "extract",
            "bvnot",
            "bvneg",
            "bvand",
            "bvor",
            "bvadd",
            "bvmul",
            "bvudiv",
            "bvurem",
            "bvshl",
            "bvlshr",
            "bvult",
            /* z3-specific bit vector theory */
            "bvsub",
            "bvxor",
            "bvslt",
            "bvule",
            "bvsle",
            "bvugt",
            "bvsgt",
            "bvuge",
            "bvsge",
            "bv2int",
            /* bit vector extras */
            "mint_signed_of_unsigned",
            /* string theory */
            "string_lt",
            "string_le",
            "string_gt",
            "string_ge",
            /* set theory */
            "smt_set_mem", "smt_miset_mem",
            "smt_set_add", "smt_miset_add",
            "smt_set_emp", "smt_miset_emp",
            "smt_set_cup", "smt_miset_cup",
            "smt_set_cap", "smt_miset_cap",
            "smt_set_com", "smt_miset_com",
            "smt_set_ele", "smt_miset_ele",
            "smt_set_dif", "smt_miset_dif",
            "smt_set_sub", "smt_miset_sub",
            "smt_set_lt", "smt_miset_lt",
            "smt_set_le", "smt_miset_le",
            /* float set theory */
            "float_set_mem",
            "float_set_add",
            "float_set_emp",
            "float_set_cup",
            "float_set_cap",
            "float_set_com",
            "float_set_ele",
            "float_set_dif",
            "float_set_sub",
            "float_set_lt",
            "float_set_le",
            /* string set theory */
            "string_set_mem",
            "string_set_add",
            "string_set_emp",
            "string_set_cup",
            "string_set_cap",
            "string_set_com",
            "string_set_ele",
            "string_set_dif",
            "string_set_sub",
            "string_set_lt",
            "string_set_le",
            /* associative sequence theory */
            "smt_seq_concat",
            "smt_seq_elem",
            "smt_seq_nil",
            "smt_seq_len",
            "smt_seq_sum",
            "smt_seq2set",
            "smt_seq_sorted",
            "smt_seq_filter",
            /* bool2int */
            "smt_bool2int");

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

        boolean result = false;
        try {
            constraint.globalContext().profiler.queryBuildTimer.start();
            CharSequence query;
            if (javaExecutionOptions.debugZ3Queries) {
                System.err.println("\nAnonymous vars in query:");
            }
            try {
                query = KILtoSMTLib.translateConstraint(constraint, SMTLIB_BUILTIN_SORTS, SMTLIB_BUILTIN_FUNCTIONS).toString();
            } finally {
                constraint.globalContext().profiler.queryBuildTimer.stop();
            }
            if (javaExecutionOptions.debugZ3Queries) {
                System.err.format("\nZ3 constraint query:\n%s\n", query);
            }
            result = z3.isUnsat(query, smtOptions.z3CnstrTimeout, formulaContext.z3Profiler);
            if (result && RuleAuditing.isAuditBegun()) {
                System.err.format("SMT query returned unsat: %s\n", query);
            }
        } catch (UnsupportedOperationException e) {
            e.printStackTrace();
            kem.registerCriticalWarning("z3 constraint query: " + e.getMessage(), e);
            if (javaExecutionOptions.debugZ3) {
                System.err.format("\nZ3 constraint warning: %s\n", e.getMessage());
            }
            formulaContext.z3Profiler.newQueryBuildFailure();
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
            try {
                left.globalContext().profiler.queryBuildTimer.start();
                CharSequence query;
                if (javaExecutionOptions.debugZ3Queries) {
                    System.err.println("\nAnonymous vars in query:");
                }
                try {
                    query = KILtoSMTLib.translateImplication(left, right, existentialQuantVars, SMTLIB_BUILTIN_SORTS, SMTLIB_BUILTIN_FUNCTIONS).toString();
                } finally {
                    left.globalContext().profiler.queryBuildTimer.stop();
                }
                if (javaExecutionOptions.debugZ3Queries) {
                    System.err.format("\nZ3 query:\n%s\n", query);
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
                    kem.registerInternalWarning(warnMsg, e);
                }
                if (javaExecutionOptions.debugZ3) {
                    System.err.format("\nZ3 warning. Query not generated: %s\n", e.getMessage());
                }
                formulaContext.queryBuildFailure();
            }
        }
        return false;
    }
}

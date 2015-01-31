// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.SMTSolver;

import java.util.Set;

import com.google.inject.Inject;
import com.google.inject.Provider;

public class SMTOperations {

    private final SMTOptions smtOptions;
    private final Z3Wrapper z3;

    @Inject
    public SMTOperations(
            Provider<Definition> definitionProvider,
            SMTOptions smtOptions,
            Z3Wrapper z3) {
        this.smtOptions = smtOptions;
        this.z3 = z3;
    }

    public boolean checkUnsat(ConjunctiveFormula constraint) {
        if (smtOptions.smt != SMTSolver.Z3) {
            return false;
        }

        if (constraint.isSubstitution()) {
            return false;
        }

        boolean result = false;
        try {
            String query = KILtoSMTLib.translateConstraint(constraint);
            result = z3.checkQuery(query, smtOptions.z3CnstrTimeout);
            if (result && RuleAuditing.isAuditBegun()) {
                System.err.println("SMT query returned unsat: " + query);
            }
        } catch (UnsupportedOperationException e) {
            e.printStackTrace();
        }
        return result;
    }

    public boolean impliesSMT(
            ConjunctiveFormula left,
            ConjunctiveFormula right,
            Set<Variable> rightOnlyVariables) {
        if (smtOptions.smt == SMTSolver.Z3) {
            try {
                return z3.checkQuery(
                        KILtoSMTLib.translateImplication(left, right, rightOnlyVariables),
                        smtOptions.z3ImplTimeout);
            } catch (UnsupportedOperationException e) {
                e.printStackTrace();
            }
        }
        return false;
    }
}

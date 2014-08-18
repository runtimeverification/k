// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.SMTLibTerm;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;


public class KILtoSMTLib extends CopyOnWriteTransformer {

    public static final ImmutableSet<Sort> supportedSorts = ImmutableSet.of(
            Sort.BOOL,
            Sort.INT,
            Sort.BIT_VECTOR,
            /* sorts manually added to the smt prelude */
            // TODO(AndreiS): generate automatically
            Sort.of("IntSet"),
            Sort.of("Tree"));
    /**
     * Flag set to true if it is sounds to skip equalities that cannot be translated.
     */
    private final boolean skipEqualities;
    private final HashSet<Variable> variables;

    public static String translateConstraint(SymbolicConstraint constraint) {
        KILtoSMTLib transformer = new KILtoSMTLib(true);
        String expression = ((SMTLibTerm) constraint.accept(transformer)).expression();
        return getConstantDeclarations(transformer.variables()) + "(assert " + expression + ")";
    }

    public static String translateImplication(
            SymbolicConstraint leftHandSide,
            SymbolicConstraint rightHandSide) {
        KILtoSMTLib leftTransformer = new KILtoSMTLib(true);
        KILtoSMTLib rightTransformer = new KILtoSMTLib(false);
        String leftExpression = ((SMTLibTerm) leftHandSide.accept(leftTransformer)).expression();
        String rightExpression = ((SMTLibTerm) rightHandSide.accept(rightTransformer)).expression();
        StringBuilder sb = new StringBuilder();
        sb.append(getConstantDeclarations(leftTransformer.variables()));
        sb.append("(assert (and ");
        sb.append(leftExpression);
        sb.append(" (not ");
        Set<Variable> rightHandSideOnlyVariables = Sets.difference(
                rightTransformer.variables(),
                leftTransformer.variables());
        if (!rightHandSideOnlyVariables.isEmpty()) {
            sb.append("(exists (");
            sb.append(getQuantifiedVariables(rightHandSideOnlyVariables));
            sb.append(") ");
        }
        sb.append(rightExpression);
        if (!rightHandSideOnlyVariables.isEmpty()) {
            sb.append(")");
        }
        sb.append(")))");
        return sb.toString();
    }

    private static String getConstantDeclarations(Set<Variable> variables) {
        StringBuilder sb = new StringBuilder();
        for (Variable variable : variables) {
            sb.append("(declare-fun ");
            // TODO(AndreiS): make sure variable names are SMTLib compliant
            sb.append(variable.name());
            sb.append(" () ");
            String sortName;
            sortName = getVariableSortName(variable);
            sb.append(sortName);
            sb.append(")\n");
        }
        return sb.toString();
    }

    private static String getQuantifiedVariables(Set<Variable> variables) {
        StringBuilder sb = new StringBuilder();
        for (Variable variable : variables) {
            sb.append("(");
            // TODO(AndreiS): make sure variable names are SMTLib compliant
            sb.append(variable.name());
            sb.append(" ");
            String sortName;
            sortName = getVariableSortName(variable);
            sb.append(sortName);
            sb.append(")\n");
        }
        return sb.toString();
    }

    private static String getVariableSortName(Variable variable) {
        return variable.sort() == Sort.BIT_VECTOR ?
               "(_ BitVec " + BitVector.getBitwidth(variable) + ")" :
               variable.sort().name();
    }

    public KILtoSMTLib(boolean skipEqualities) {
        this.skipEqualities = skipEqualities;
        variables = new HashSet<>();
    }

    /**
     * Returns an unmodifiable view of the sets of variables occurring during the translation.
     */
    public Set<Variable> variables() {
        return Collections.unmodifiableSet(variables);
    }

    /**
     * Translates the equalities of the given symbolic constraint into SMTLib format.
     * Ignores the substitution of the symbolic constraint.
     */
    @Override
    public ASTNode transform(SymbolicConstraint constraint) {
        if (constraint.data.equalities.isEmpty()) {
            return new SMTLibTerm("true");
        }

        StringBuilder sb = new StringBuilder();
        sb.append("(and");
        boolean isEmptyAdd = true;
        for (SymbolicConstraint.Equality equality : constraint.data.equalities) {
            try {
                String left = ((SMTLibTerm) equality.leftHandSide().accept(this)).expression();
                String right = ((SMTLibTerm) equality.rightHandSide().accept(this)).expression();
                sb.append(" (= ");
                sb.append(left);
                sb.append(" ");
                sb.append(right);
                sb.append(")");
                isEmptyAdd = false;
            } catch (UnsupportedOperationException e) {
                // TODO(AndreiS): fix this translation and the exceptions
                if (skipEqualities){
                    /* it is sound to skip the equalities that cannot be translated */
                    e.printStackTrace();
                } else {
                    throw e;
                }
            }
        }
        if (isEmptyAdd) {
            sb.append(" true");
        }
        sb.append(")");
        return new SMTLibTerm(sb.toString());
    }

    @Override
    public ASTNode transform(KItem kItem) {
        if (!(kItem.kLabel() instanceof KLabelConstant)) {
            throw new UnsupportedOperationException();
        }
        KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();

        if (!(kItem.kList() instanceof KList)) {
            throw new UnsupportedOperationException();
        }
        KList kList = (KList) kItem.kList();

        if (kList.hasFrame()) {
            throw new UnsupportedOperationException();
        }

        String label = kLabel.smtlib();
        if (label == null) {
            throw new UnsupportedOperationException("missing SMTLib translation for " + kLabel);
        }

        List<Term> arguments;
        switch (label) {
            case "exists":
                Variable variable = (Variable) kList.get(0);
                label = "exists ((" + variable.name() + " " + variable.sort() + ")) ";
                arguments = ImmutableList.of(kList.get(1));
                break;
            case "extract":
                int beginIndex = ((IntToken) kList.get(1)).intValue();
                int endIndex = ((IntToken) kList.get(2)).intValue() - 1;
                label = "(_ extract " + endIndex + " " + beginIndex + ")";
                arguments = ImmutableList.of(kList.get(0));
                break;
            case "concat":
                arguments = ImmutableList.of(kList.get(1), kList.get(0));
                break;
            default:
                arguments = kList.getContents();
        }

        if (!arguments.isEmpty()) {
            StringBuilder sb = new StringBuilder();
            sb.append("(");
            sb.append(label);
            for (Term argument : arguments) {
                sb.append(" ");
                sb.append(((SMTLibTerm) argument.accept(this)).expression());
            }
            sb.append(")");
            return new SMTLibTerm(sb.toString());
        } else {
            return new SMTLibTerm(label);
        }
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return new SMTLibTerm(Boolean.toString(boolToken.booleanValue()));
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return new SMTLibTerm(Integer.toString(intToken.intValue()));
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        StringBuilder sb = new StringBuilder();
        sb.append("#b");
        for (int i = bitVector.bitwidth() - 1; i >= 0; --i) {
            BigInteger value = bitVector.unsignedValue();
            sb.append(value.testBit(i) ? "1" : "0");
        }
        return new SMTLibTerm(sb.toString());
    }

    @Override
    public ASTNode transform(Variable variable) {
        if (!supportedSorts.contains(variable.sort())) {
            throw new UnsupportedOperationException();
        }
        variables.add(variable);
        return new SMTLibTerm(variable.name());
    }

}

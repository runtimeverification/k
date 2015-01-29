// Copyright (c) 2013-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.rewritemachine.GenerateRHSInstructions;
import org.kframework.backend.java.rewritemachine.RHSInstruction;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.io.Serializable;
import java.util.List;

/**
 * The uninterpreted version of a symbolic constraint. Used merely as a
 * container for equalities between terms.
 *
 * @see org.kframework.backend.java.symbolic.SymbolicConstraint
 *
 * @author AndreiS
 */
public class UninterpretedConstraint extends JavaSymbolicObject {

    /**
     * An equality between terms. Used merely to store the left-hand side and
     * the right-hand side of the equality.
     */
    public static class Equality implements Serializable {

        public static final String SEPARATOR = " = ";

        private final Term leftHandSide;
        private final Term rightHandSide;
        private final ImmutableList<RHSInstruction> instructions;
        private int hashCode;

        private Equality(Term leftHandSide, Term rightHandSide, ImmutableList<RHSInstruction> instructions) {
            this.leftHandSide = leftHandSide;
            this.rightHandSide = rightHandSide;
            this.instructions = instructions;
        }

        public Term leftHandSide() {
            return leftHandSide;
        }

        public Term rightHandSide() {
            return rightHandSide;
        }

        public List<RHSInstruction> instructions() {
            return instructions;
        }

        @Override
        public boolean equals(Object object) {
            if (this == object) {
                return true;
            }

            if (!(object instanceof Equality)) {
                return false;
            }

            Equality equality = (Equality) object;
            return leftHandSide.equals(equality.leftHandSide)
                   && rightHandSide.equals(equality.rightHandSide);
        }

        @Override
        public int hashCode() {
            if (hashCode == Utils.NO_HASHCODE) {
                hashCode = 1;
                hashCode = hashCode * Utils.HASH_PRIME + leftHandSide.hashCode();
                hashCode = hashCode * Utils.HASH_PRIME + rightHandSide.hashCode();
            }
            return hashCode;
        }

        @Override
        public String toString() {
            return leftHandSide + SEPARATOR + rightHandSide;
        }

    }

    public static final String SEPARATOR = " /\\ ";

    private static final Joiner joiner = Joiner.on(SEPARATOR);

    private final ImmutableList<Equality> equalities;

    private UninterpretedConstraint(ImmutableList<Equality> equalities) {
        this.equalities = equalities;
    }

    public List<Equality> equalities() {
        return equalities;
    }

    /**
     * Returns the interpreted counterpart of this constraint.
     *
     * @param context
     *            the term context
     * @return the corresponding symbolic constraint
     */
    public SymbolicConstraint getSymbolicConstraint(TermContext context) {
        SymbolicConstraint symbolicConstraint = new SymbolicConstraint(context);
        for (Equality equality : equalities) {
            symbolicConstraint.add(equality.leftHandSide, equality.rightHandSide);
        }
        return symbolicConstraint;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof UninterpretedConstraint)) {
            return false;
        }

        UninterpretedConstraint constraint = (UninterpretedConstraint) object;
        return equalities.equals(constraint.equalities);
    }

    @Override
    public int hashCode() {
        if (hashCode == Utils.NO_HASHCODE) {
            hashCode = equalities.hashCode();
        }
        return hashCode;
    }

    @Override
    public String toString() {
        return joiner.join(equalities);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    public static Builder builder() {
        return new Builder();
    }

    public static class Builder {

        private final ImmutableList.Builder<Equality> equalitiesBuilder = ImmutableList.builder();

        public void add(Term leftHandSide, Term rightHandSide, TermContext context) {
            GenerateRHSInstructions visitor = new GenerateRHSInstructions(context);
            leftHandSide.accept(visitor);
            equalitiesBuilder.add(new Equality(leftHandSide, rightHandSide,
                    visitor.getInstructions()));
        }

        public UninterpretedConstraint build() {
            return new UninterpretedConstraint(equalitiesBuilder.build());
        }
    }

}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import com.google.common.base.Joiner;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
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
    public class Equality implements Serializable {

        public static final String SEPARATOR = " = ";

        private final Term leftHandSide;
        private final Term rightHandSide;

        private Equality(Term leftHandSide, Term rightHandSide) {
            this.leftHandSide = leftHandSide;
            this.rightHandSide = rightHandSide;
        }

        public Term leftHandSide() {
            return leftHandSide;
        }

        public Term rightHandSide() {
            return rightHandSide;
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
            int hash = 1;
            hash = hash * Utils.HASH_PRIME + leftHandSide.hashCode();
            hash = hash * Utils.HASH_PRIME + rightHandSide.hashCode();
            return hash;
        }

        @Override
        public String toString() {
            return leftHandSide + SEPARATOR + rightHandSide;
        }

    }

    public static final String SEPARATOR = " /\\ ";

    private static final Joiner joiner = Joiner.on(SEPARATOR);

    private final List<Equality> equalities = new ArrayList<Equality>();

    public void add(Term leftHandSide, Term rightHandSide) {
        equalities.add(new Equality(leftHandSide, rightHandSide));
    }

    public void addAll(UninterpretedConstraint constraint) {
        for (Equality eq : constraint.equalities) {
            equalities.add(eq);
        }
    }

    /**
     * @return an unmodifiable view of the equalities
     */
    public List<Equality> equalities() {
        return Collections.unmodifiableList(equalities);
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
        if (hashCode == 0) {
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

    public UninterpretedConstraint deepCopy() {
        UninterpretedConstraint result = new UninterpretedConstraint();
        result.equalities.addAll(equalities);
        return result;        
    }
}

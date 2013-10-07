package org.kframework.backend.java.symbolic;

import com.google.common.base.Joiner;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.ASTNode;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * @author AndreiS
 */
public class UninterpretedConstraint extends JavaSymbolicObject {

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

    public Collection<Equality> equalities() {
        return Collections.unmodifiableList(equalities);
    }

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
        return equalities.hashCode();
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

}

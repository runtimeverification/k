package org.kframework.backend.java.symbolic;


import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableSet;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.Sorted;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * A conjunction of equalities between terms (with variables).
 *
 * @author AndreiS
 */
public class SymbolicConstraint implements Serializable, Visitable {

    public enum TruthValue { TRUE, UNKNOWN, FALSE }

    /**
     * An equality between two terms (with variables).
     */
    public class Equality implements Serializable {

        public static final String SEPARATOR = " =? ";

        private Term leftHandSide;
        private Term rightHandSide;

        private Equality(Term leftHandSide, Term rightHandSide) {
            assert leftHandSide.kind().equals(rightHandSide.kind()):
                    "kind mismatch between "
                    + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                    + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

            this.leftHandSide = leftHandSide;
            this.rightHandSide = rightHandSide;
        }

        public Equality evaluate() {
            leftHandSide = leftHandSide.evaluate(context);
            rightHandSide = rightHandSide.evaluate(context);
            return this;
        }

        public Term leftHandSide() {
            return leftHandSide;
        }

        public Term rightHandSide() {
            return rightHandSide;
        }

        public boolean isFalse() {
            if (leftHandSide.isGround() && rightHandSide.isGround()) {
                return !leftHandSide.equals(rightHandSide);
            }

            if (!(leftHandSide instanceof Sorted) || !(rightHandSide instanceof Sorted)) {
                return false;
            }

            if (leftHandSide instanceof KItem
                    && ((KItem) leftHandSide).kLabel().isConstructor()) {
                return !context.isSubsortedEq(
                        ((Sorted) rightHandSide).sort(),
                        ((KItem) leftHandSide).sort());
            } else if (rightHandSide instanceof KItem
                    && ((KItem) rightHandSide).kLabel().isConstructor()) {
                return !context.isSubsortedEq(
                        ((Sorted) leftHandSide).sort(),
                        ((KItem) rightHandSide).sort());
            } else {
                return null == context.getGLBSort(ImmutableSet.<String>of(
                    ((Sorted) leftHandSide).sort(),
                    ((Sorted) rightHandSide).sort()));
            }
        }

        public boolean isTrue() {
            return leftHandSide.equals(rightHandSide);
        }

        public boolean isUnknown() {
            return !isTrue() && !isFalse();
        }

        private Equality substitute(Map<Variable, ? extends Term> substitution) {
            leftHandSide = leftHandSide.substitute(substitution, context);
            rightHandSide = rightHandSide.substitute(substitution, context);
            return this;
        }

        private Equality substitute(Variable variable, Term term) {
            return substitute(Collections.singletonMap(variable, term));
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
        public String toString() {
            return leftHandSide + SEPARATOR + rightHandSide;
        }

    }

    public static final String SEPARATOR = " /\\ ";

    private static final Joiner joiner = Joiner.on(SEPARATOR);
    private static final Joiner.MapJoiner substitutionJoiner
            = joiner.withKeyValueSeparator(Equality.SEPARATOR);

    private final LinkedList<Equality> equalities = new LinkedList<Equality>();
    private boolean isNormal;
    private final Map<Variable, Term> substitution = new HashMap<Variable, Term>();
    private TruthValue truthValue;

    private Context context;
    
    public SymbolicConstraint(Context context) {
    	this.context = context;
        truthValue = TruthValue.TRUE;
        isNormal = true;
    }
    
    public TruthValue add(Term leftHandSide, Term rightHandSide) {
        assert leftHandSide.kind().equals(rightHandSide.kind()):
                "kind mismatch between "
                        + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                        + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

        leftHandSide = leftHandSide.substitute(substitution, context);
        //if (leftHandSide.isGround()) {
            leftHandSide = leftHandSide.evaluate(context);
        //}
        rightHandSide = rightHandSide.substitute(substitution, context);
        //if (rightHandSide.isGround()) {
            rightHandSide = rightHandSide.evaluate(context);
        //}

        Equality equality = this.new Equality(leftHandSide, rightHandSide);

        if (equality.isUnknown()){
            equalities.add(equality);
            truthValue = TruthValue.UNKNOWN;
            isNormal = false;
        } else if (equality.isFalse()) {
            equalities.add(equality);
            truthValue = TruthValue.FALSE;
        }

        return truthValue;
    }

    public TruthValue addAll(SymbolicConstraint constraint) {
        for (Map.Entry<Variable, Term> entry : constraint.substitution.entrySet()) {
            add(entry.getKey(), entry.getValue());
        }

        for (Equality equality : constraint.equalities) {
            add(equality.leftHandSide, equality.rightHandSide);
        }

        return truthValue;
    }

    public List<Equality> equalities() {
        normalize();
        return Collections.unmodifiableList(equalities);
    }

    public Map<Variable, Term> substitution() {
        normalize();
        return Collections.unmodifiableMap(substitution);
    }

    public TruthValue getTruthValue() {
        normalize();
        return truthValue;
    }

    public boolean isFalse() {
        normalize();
        return truthValue == TruthValue.FALSE;
    }

    public boolean isTrue() {
        normalize();
        return truthValue == TruthValue.TRUE;
    }

    public boolean isUnknown() {
        normalize();
        return truthValue == TruthValue.UNKNOWN;
    }

    private void normalize() {
        if (isNormal) {
            return;
        }
        isNormal = true;

        for (Iterator<Equality> iterator = equalities.iterator(); iterator.hasNext();) {
            Equality equality = iterator.next();
            equality.substitute(substitution).evaluate();

            if (equality.isTrue()) {
                iterator.remove();
                continue;
            } else if (equality.isFalse()) {
                truthValue = TruthValue.FALSE;
                return;
            }

            Variable variable;
            Term term;
            /* when possible, substitute the variables in the RHS in terms of the variables in the
             * LHS */
            if (equality.rightHandSide instanceof Variable) {
                variable = (Variable) equality.rightHandSide;
                term = equality.leftHandSide;
            } else if (equality.leftHandSide instanceof Variable) {
                variable = (Variable) equality.leftHandSide;
                term = equality.rightHandSide;
            } else {
                continue;
            }
            if (term.variableSet().contains(variable)) {
                continue;
            }

            Map<Variable, Term> tempSubstitution = new HashMap<Variable, Term>();
            tempSubstitution.put(variable, term);

            SymbolicConstraint.compose(substitution, tempSubstitution, context);
            substitution.put(variable, term);

            for (Iterator<Equality> previousIterator = equalities.iterator(); previousIterator.hasNext();) {
                Equality previousEquality = previousIterator.next();
                if (previousEquality == equality) {
                    break;
                }
                previousEquality.substitute(tempSubstitution);

                if (previousEquality.isTrue()) {
                    previousIterator.remove();
                } else if (previousEquality.isFalse()) {
                    truthValue = TruthValue.FALSE;
                    return;
                }
            }
            iterator.remove();
        }
    }

    @Override
    public String toString() {
        if (truthValue == TruthValue.TRUE) {
            return "true";
        }

        if (truthValue == TruthValue.FALSE) {
            return "false";
        }

        StringBuilder builder = new StringBuilder();
        builder = joiner.appendTo(builder, equalities);
        if (!(builder.length() == 0) && !substitution.isEmpty()) {
            builder.append(SEPARATOR);
        }
        builder = substitutionJoiner.appendTo(builder, substitution);
        return builder.toString();
    }
    @SuppressWarnings("unchecked")
    public static void compose(Map<Variable, Term> map, Map<Variable, Term> substitution, Context context) {
        Map.Entry<Variable, Term>[] entries = map.entrySet().toArray(new Map.Entry[map.size()]);
        for (int index = 0; index < entries.length; ++index) {
            Term term = entries[index].getValue().substitute(substitution, context);
            if (term != entries[index].getValue()) {
                map.put(entries[index].getKey(), term);
            }
        }
    }

    public Map<Variable, Variable> rename(Set<Variable> variableSet) {
        Map<Variable, Variable> substitution = Variable.getFreshSubstitution(variableSet);

        for (Variable variable : variableSet) {
            if (this.substitution.get(variable) != null) {
                this.substitution.put(
                        substitution.get(variable),
                        this.substitution.remove(variable).substitute(substitution, context));
            }
        }

        for (Equality equality : equalities) {
            equality.substitute(substitution);
        }

        return substitution;
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

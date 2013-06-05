package org.kframework.backend.java.symbolic;


import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableSet;
import org.kframework.backend.java.kil.AnonymousVariable;
import org.kframework.backend.java.kil.Sorted;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 *
 * @author AndreiS
 */
public class SymbolicConstraint {

    public enum TruthValue { TRUE, UNKNOWN, FALSE }

    public class Equality {

        public static final String SEPARATOR = " =? ";

        private Term leftHandSide;
        private Term rightHandSide;

        private Equality(Term leftHandSide, Term rightHandSide) {
            assert leftHandSide.getKind().equals(rightHandSide.getKind()):
                    "kind mismatch between "
                    + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                    + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

            this.leftHandSide = leftHandSide;
            this.rightHandSide = rightHandSide;
        }

        public Term getLeftHandSide() {
            return leftHandSide;
        }

        public Term getRightHandSide() {
            return rightHandSide;
        }

        public boolean isFalse() {
            if (leftHandSide instanceof Sorted && rightHandSide instanceof Sorted) {
                return null == context.getGLBSort(ImmutableSet.<String>of(
                        ((Sorted) leftHandSide).sort(),
                        ((Sorted) rightHandSide).sort()));
            } else {
                return false;
            }
        }

        public boolean isTrue() {
            return leftHandSide.equals(rightHandSide);
        }

        public boolean isUnknown() {
            return !isTrue() && !isFalse();
        }

        private void substitute(Map<Variable, Term> substitution) {
            leftHandSide = leftHandSide.substitute(substitution, context);
            rightHandSide = rightHandSide.substitute(substitution, context);
        }

        private void substitute(Variable variable, Term term) {
            Map<Variable, Term> substitution = new HashMap<Variable, Term>();
            substitution.put(variable, term);
            substitute(substitution);
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

    protected Context context;
    
    public SymbolicConstraint(Context context) {
    	this.context = context;
        truthValue = TruthValue.TRUE;
        isNormal = true;
    }
    
    public TruthValue add(Term leftHandSide, Term rightHandSide) {
        assert leftHandSide.getKind().equals(rightHandSide.getKind()):
                "kind mismatch between "
                        + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                        + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

        leftHandSide = leftHandSide.substitute(substitution, context);
        rightHandSide = rightHandSide.substitute(substitution, context);

        Equality equality = this.new Equality(leftHandSide, rightHandSide);

        if (equality.isUnknown()){
            equalities.add(equality);
            truthValue = TruthValue.UNKNOWN;
            isNormal = false;
        } else if (equality.isFalse()) {
            //equalities.add(equality);
            truthValue = TruthValue.FALSE;
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
            equality.substitute(substitution);

            if (equality.isTrue()) {
                iterator.remove();
                continue;
            } else if (equality.isFalse()) {
                truthValue = TruthValue.FALSE;
                return;
            }

            Variable variable;
            Term term;
            if (equality.leftHandSide instanceof Variable) {
                variable = (Variable) equality.leftHandSide;
                term = equality.rightHandSide;
            } else if (equality.rightHandSide instanceof Variable) {
                variable = (Variable) equality.rightHandSide;
                term = equality.leftHandSide;
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
                    continue;
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

    public Map<Variable, Term> freshSubstitution(Set<Variable> variableSet) {
        Map<Variable, Term> freshSubstitution = new HashMap<Variable, Term>();

        for (Variable variable : variableSet) {
            if (substitution.get(variable) != null) {
                substitution.put(AnonymousVariable.getFreshVariable(variable.sort()),
                                 substitution.remove(variable));
            } else {
                freshSubstitution.put(variable,
                                      AnonymousVariable.getFreshVariable(variable.sort()));
            }
        }

        for (Equality equality : equalities) {
            equality.substitute(freshSubstitution);
        }

        return freshSubstitution;
    }

}

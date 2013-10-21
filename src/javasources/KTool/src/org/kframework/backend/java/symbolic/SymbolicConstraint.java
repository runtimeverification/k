package org.kframework.backend.java.symbolic;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sorted;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.kil.Z3Term;
import org.kframework.backend.java.util.GappaPrinter;
import org.kframework.backend.java.util.GappaServer;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.kil.ASTNode;

import java.io.Serializable;
import java.util.*;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableSet;

import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.K;


/**
 * A conjunction of equalities between terms (with variables).
 *
 * @author AndreiS
 */
public class SymbolicConstraint extends JavaSymbolicObject {

    public enum TruthValue { TRUE, UNKNOWN, FALSE }

    /**
     * An equality between two terms (with variables).
     */
    public class Equality {

        public static final String SEPARATOR = " =? ";

        private Term leftHandSide;
        private Term rightHandSide;

        private Equality(Term leftHandSide, Term rightHandSide) {
            if (leftHandSide instanceof Bottom) rightHandSide = leftHandSide;
            if (rightHandSide instanceof Bottom) leftHandSide = rightHandSide;
            assert leftHandSide.kind() == rightHandSide.kind()
                    || ((leftHandSide.kind() == Kind.KITEM || leftHandSide.kind() == Kind.K
                         || leftHandSide.kind() == Kind.KLIST)
                        && (rightHandSide.kind() == Kind.KITEM || rightHandSide.kind() == Kind.K
                            || rightHandSide.kind() == Kind.KLIST)):
                    "kind mismatch between "
                    + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                    + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

            if (leftHandSide.kind() == Kind.K || leftHandSide.kind() == Kind.KLIST) {
                leftHandSide = KCollection.downKind(leftHandSide);
            }
            if (rightHandSide.kind() == Kind.K || rightHandSide.kind() == Kind.KLIST) {
                rightHandSide = KCollection.downKind(rightHandSide);
            }

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
            if (leftHandSide instanceof Bottom || rightHandSide instanceof Bottom)
                return true;
            if (leftHandSide.isGround() && rightHandSide.isGround()) {
                return !leftHandSide.equals(rightHandSide);
            }

            if (!(leftHandSide instanceof Sorted) || !(rightHandSide instanceof Sorted)) {
                return false;
            }

            if (leftHandSide instanceof KItem
                    && ((KItem) leftHandSide).kLabel().isConstructor()) {
                return !definition.context().isSubsortedEq(
                        ((Sorted) rightHandSide).sort(),
                        ((KItem) leftHandSide).sort());
            } else if (rightHandSide instanceof KItem
                    && ((KItem) rightHandSide).kLabel().isConstructor()) {
                return !definition.context().isSubsortedEq(
                        ((Sorted) leftHandSide).sort(),
                        ((KItem) rightHandSide).sort());
            } else {
                return null == definition.context().getGLBSort(ImmutableSet.<String>of(
                    ((Sorted) leftHandSide).sort(),
                    ((Sorted) rightHandSide).sort()));
            }
        }

        public boolean isTrue() {
            if (leftHandSide  instanceof Bottom || rightHandSide instanceof Bottom) return false;
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
    private final TermContext context;
    private final Definition definition;
    private final SymbolicUnifier unifier;

    public SymbolicConstraint(TermContext context) {
        this.context = context;
        this.definition = context.definition();
        unifier = new SymbolicUnifier(this, context);
        truthValue = TruthValue.TRUE;
        isNormal = true;
    }
    
    public TruthValue add(Term leftHandSide, Term rightHandSide) {
        assert leftHandSide.kind() == rightHandSide.kind()
                || ((leftHandSide.kind() == Kind.KITEM || leftHandSide.kind() == Kind.K
                     || leftHandSide.kind() == Kind.KLIST)
                    && (rightHandSide.kind() == Kind.KITEM || rightHandSide.kind() == Kind.K
                        || rightHandSide.kind() == Kind.KLIST)):
                "kind mismatch between "
                + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

        Term normalizedLeftHandSide = leftHandSide.substitute(substitution, context);
        if (normalizedLeftHandSide != leftHandSide) {
            normalizedLeftHandSide = normalizedLeftHandSide.evaluate(context);
        }

        Term normalizedRightHandSide = rightHandSide.substitute(substitution, context);
        if (normalizedRightHandSide != rightHandSide) {
            normalizedRightHandSide = normalizedRightHandSide.evaluate(context);
        }

        Equality equality = this.new Equality(normalizedLeftHandSide, normalizedRightHandSide);
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

    public TruthValue addAll(Collection<Term> condition) {
        for (Term term : condition) {
            add(term, BoolToken.TRUE);
        }

        return truthValue;
    }

    public TruthValue addAll(SymbolicConstraint constraint) {
        for (Map.Entry<Variable, Term> entry : constraint.substitution.entrySet()) {
            add(entry.getValue(), entry.getKey());
        }

        for (Equality equality : constraint.equalities) {
            add(equality.leftHandSide, equality.rightHandSide);
        }

        return truthValue;
    }

    public boolean checkUnsat() {
        if (!K.smt.equals("z3")) {
            return false;
        }

        normalize();
        Boolean result = false;
        try {
            com.microsoft.z3.Context context = Z3Wrapper.newContext();
            KILtoZ3 transformer = new KILtoZ3(Collections.<Variable>emptySet(), context);
            Solver solver = context.MkSolver();
            for (Equality equality : equalities) {
                solver.Assert(context.MkEq(
                        ((Z3Term) equality.leftHandSide.accept(transformer)).expression(),
                        ((Z3Term) equality.rightHandSide.accept(transformer)).expression()));
            }
            result = solver.Check() == Status.UNSATISFIABLE;
            context.Dispose();
        } catch (Z3Exception e) {
            e.printStackTrace();
        } catch (RuntimeException e) {
            // TODO(AndreiS): fix this translation and the exceptions
            e.printStackTrace();
        }
        return result;
    }

    public List<Equality> equalities() {
        normalize();
        return Collections.unmodifiableList(equalities);
    }

    public Map<Variable, Term> substitution() {
        normalize();
        return Collections.unmodifiableMap(substitution);
    }

    public void eliminateAnonymousVariables() {
        for (Iterator<Variable> iterator = substitution.keySet().iterator(); iterator.hasNext();) {
            Variable variable = iterator.next();
            if (variable.isAnonymous()) {
                iterator.remove();
            }
        }
    }

    public TruthValue getTruthValue() {
        normalize();
        return truthValue;
    }

    public boolean implies(SymbolicConstraint constraint) {
        normalize();
        Boolean result = false;

        if (K.smt.equals("gappa")) {
            constraint.normalize();
            System.out.println("Verifying whether " + toString() + "\n implies " + constraint.toString());
            ListIterator<Equality> listIterator = constraint.equalities().listIterator();
            while (listIterator.hasNext()) {
                Equality e2 = listIterator.next();
                for (Equality e1 : equalities()) {
                    if (e2.equals(e1)) {
                        listIterator.remove();
                        break;
                    }
                }
            }
            if (constraint.equalities().isEmpty()) return true;
            String gterm1 = GappaPrinter.toGappa(this);
            String gterm2 = GappaPrinter.toGappa(constraint);
            String input = "(" + gterm2 + ")";
            if (!gterm1.equals("")) input = "(" + gterm1 + ") -> " + input;
            if (GappaServer.proveTrue(input))
                result = true;

//            System.out.println(constraint);
        } else if (K.smt.equals("z3")) {
            Set<Variable> rightHandSideVariables = new HashSet<Variable>(constraint.variableSet());
            rightHandSideVariables.removeAll(variableSet());

            try {
                com.microsoft.z3.Context context = Z3Wrapper.newContext();
                KILtoZ3 transformer = new KILtoZ3(rightHandSideVariables, context);

                Solver solver = context.MkSolver();

                for (Equality equality : equalities) {
                    solver.Assert(context.MkEq(
                            ((Z3Term) equality.leftHandSide.accept(transformer)).expression(),
                            ((Z3Term) equality.rightHandSide.accept(transformer)).expression()));
                }

                //BoolExpr[] inequalities = new BoolExpr[constraint.equalities.size() + constraint.substitution.size()];
                BoolExpr[] inequalities = new BoolExpr[constraint.equalities.size()];
                int i = 0;
                for (Equality equality : constraint.equalities) {
                    inequalities[i++] = context.MkNot(context.MkEq(
                            ((Z3Term) equality.leftHandSide.accept(transformer)).expression(),
                            ((Z3Term) equality.rightHandSide.accept(transformer)).expression()));
                }
                /* TODO(AndreiS): fix translation to smt
            for (Map.Entry<Variable, Term> entry : constraint.substitution.entrySet()) {
                inequalities[i++] = context.MkNot(context.MkEq(
                        ((Z3Term) entry.getKey().accept(transformer)).expression(),
                        ((Z3Term) entry.getValue().accept(transformer)).expression()));
            }
            */

                Sort[] variableSorts = new Sort[rightHandSideVariables.size()];
                Symbol[] variableNames = new Symbol[rightHandSideVariables.size()];
                i = 0;
                for (Variable variable : rightHandSideVariables) {
                    if (variable.sort().equals(BoolToken.SORT_NAME)) {
                        variableSorts[i] = context.MkBoolSort();
                    } else if (variable.sort().equals(IntToken.SORT_NAME)) {
                        variableSorts[i] = context.MkIntSort();
                    } else if (variable.sort().equals(Int32Token.SORT_NAME)) {
                        variableSorts[i] = context.MkBitVecSort(32);
                    } else {
                        throw new RuntimeException();
                    }
                    variableNames[i] = context.MkSymbol(variable.name());
                    ++i;
                }

                Expr[] boundVariables = new Expr[rightHandSideVariables.size()];
                i = 0;
                for (Variable variable : rightHandSideVariables) {
                    boundVariables[i++] = KILtoZ3.valueOf(variable, context).expression();
                }

                if (boundVariables.length > 0) {
                    solver.Assert(context.MkForall(
                            boundVariables,
                            context.MkOr(inequalities),
                            1,
                            null,
                            null,
                            null,
                            null));
                } else {
                    solver.Assert(context.MkOr(inequalities));
                }

                result = solver.Check() == Status.UNSATISFIABLE;
                context.Dispose();
            } catch (Z3Exception e) {
                e.printStackTrace();
            }
        }
        return result;
    }

    public boolean isFalse() {
        normalize();
        return truthValue == TruthValue.FALSE;
    }

    public boolean isTrue() {
        normalize();
        return truthValue == TruthValue.TRUE;
    }

    public boolean isSubstitution() {
        normalize();
        return equalities.isEmpty() && unifier.multiConstraints.isEmpty();
    }

    public boolean isUnknown() {
        normalize();
        return truthValue == TruthValue.UNKNOWN;
    }

    public Collection<SymbolicConstraint> getMultiConstraints() {
        if (!unifier.multiConstraints.isEmpty()) {
            assert unifier.multiConstraints.size() == 1;

            List<SymbolicConstraint> multiConstraints = new ArrayList<SymbolicConstraint>();
            for (SymbolicConstraint constraint : unifier.multiConstraints.iterator().next()) {
                constraint.addAll(this);
                multiConstraints.add(constraint);
            }
            return multiConstraints;
        } else {
            return Collections.singletonList(this);
        }
    }

    public TruthValue simplify() {
        boolean change;
        label: do {
            change = false;
            normalize();

            for (int i = 0; i < equalities.size(); ++i) {
                Equality equality = equalities.get(i);
                if (!equality.leftHandSide.isSymbolic() && !equality.rightHandSide.isSymbolic()) {
                    equalities.remove(i);
                    if (!unifier.unify(equality)) {
                        truthValue = TruthValue.FALSE;
                        break label;
                    }

                    change = true;
                }
            }
        } while (change);

        return truthValue;
    }

    private void normalize() {
        if (isNormal) {
            return;
        }
        isNormal = true;
        Set<Equality> equalitiesToRemove = new HashSet<Equality>();
        for (Iterator<Equality> iterator = equalities.iterator(); iterator.hasNext();) {
            Equality equality = iterator.next();
            equality.substitute(substitution);
            //TODO(AndreiS): Only evaluate if the term has changed
            equality.evaluate();

            if (equality.isTrue()) {
                equalitiesToRemove.add(equality);
                continue;
            } else if (equality.isFalse()) {
                truthValue = TruthValue.FALSE;
                return;
            }

            Variable variable;
            Term term;
            // TODO(AndreiS): the sort of a variable may become more specific
            /* when possible, substitute the anonymous variable */
            if (equality.leftHandSide instanceof Variable
                    && equality.rightHandSide instanceof Variable
                    && ((Variable) equality.rightHandSide).isAnonymous()) {
                variable = (Variable) equality.rightHandSide;
                term = equality.leftHandSide;
            } else if (equality.leftHandSide instanceof Variable) {
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
                //TODO(AndreiS): Only evaluate if the term has changed
                previousEquality.evaluate();
                if (previousEquality.isTrue()) {
                    equalitiesToRemove.add(previousEquality);
                } else if (previousEquality.isFalse()) {
                    truthValue = TruthValue.FALSE;
                    return;
                }
            }
            equalitiesToRemove.add(equality);
        }
        for (Iterator<Equality> iterator = equalitiesToRemove.iterator(); iterator.hasNext();) {
            Equality equality = iterator.next();
            equalities.remove(equality);
            iterator.remove();
        }
        assert equalitiesToRemove.size() == 0;
    }

    @SuppressWarnings("unchecked")
    public static void compose(
            Map<Variable, Term> map,
            Map<Variable, Term> substitution,
            TermContext context) {
        Map.Entry<Variable, Term>[] entries = map.entrySet().toArray(new Map.Entry[map.size()]);
        for (Map.Entry<Variable, Term> entry : entries) {
            Term term = entry.getValue().substitute(substitution, context);
            if (term != entry.getValue()) {
                map.put(entry.getKey(), term);
            }
        }
    }

    public Map<Variable, Variable> rename(Set<Variable> variableSet) {
        Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(variableSet);

        /* rename substitution keys */
        for (Variable variable : variableSet) {
            if (substitution.get(variable) != null) {
                substitution.put(freshSubstitution.get(variable), substitution.remove(variable));
            }
        }

        /* rename in substitution values */
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            entry.setValue(entry.getValue().substitute(freshSubstitution, context));
        }

        for (Equality equality : equalities) {
            equality.substitute(freshSubstitution);
        }

        return freshSubstitution;
    }

    /**
     * Returns a new {@code SymbolicConstraint} instance obtained from this symbolic constraint
     * by applying substitution.
     */
    public SymbolicConstraint substitute(Map<Variable, ? extends Term> substitution, TermContext context) {
        if (substitution.isEmpty()) {
            return this;
        }

        return (SymbolicConstraint) accept(new SubstitutionTransformer(substitution, context));
    }

    /**
     * Returns a new {@code SymbolicConstraint} instance obtained from this symbolic constraint by
     * substituting variable with term.
     */
    public SymbolicConstraint substitute(Variable variable, Term term, TermContext context) {
        return substitute(Collections.singletonMap(variable, term), context);
    }

    @Override
    public boolean equals(Object object) {
        // TODO(AndreiS): normalize
        if (this == object) {
            return true;
        }

        if (!(object instanceof SymbolicConstraint)) {
            return false;
        }

        SymbolicConstraint constraint = (SymbolicConstraint) object;
        return equalities.equals(constraint.equalities)
               && substitution.equals(constraint.substitution);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + equalities.hashCode();
        hash = hash * Utils.HASH_PRIME + substitution.hashCode();
        return hash;
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


    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(org.kframework.kil.visitors.Transformer transformer)
            throws TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(org.kframework.kil.visitors.Visitor visitor) {
        throw new UnsupportedOperationException();
    }

    public static class Bottom extends Term {
        public Bottom() {
            super(Kind.BOTTOM);
        }

        @Override
        public boolean isSymbolic() {
            return false;
        }

        @Override
        public ASTNode accept(Transformer transformer) {
            return this;
        }

        @Override
        public void accept(Unifier unifier, Term patten) {
        }

        @Override
        public void accept(Visitor visitor) {
        }
    }
}

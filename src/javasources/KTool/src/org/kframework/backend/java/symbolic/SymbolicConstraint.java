package org.kframework.backend.java.symbolic;


import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.util.GappaPrinter;
import org.kframework.backend.java.util.GappaServer;
import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.kil.ASTNode;

import java.io.Serializable;
import java.util.*;
import java.util.Collection;

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
    private static final boolean DEBUG = true;

    public void orientSubstitution(Set<Variable> variables, TermContext termContext) {
        Map<Variable, Term> newSubstitution = new HashMap<>();
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            if (variables.contains(entry.getValue())) {
                newSubstitution.put((Variable) entry.getValue(), entry.getKey());
            }
        }

        Map<Variable, Term> result = new HashMap<>();
        for (Map.Entry<Variable, Term> entry : newSubstitution.entrySet()) {
            substitution.remove(entry.getValue());
            result.put(entry.getKey(), entry.getValue().substitute(newSubstitution, termContext));
        }
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            result.put(entry.getKey(), entry.getValue().substitute(newSubstitution, termContext));
        }

        substitution = result;
    }

    public enum TruthValue { TRUE, UNKNOWN, FALSE }


    public class Implication {
        SymbolicConstraint left;
        SymbolicConstraint right;

        public Implication(SymbolicConstraint left, SymbolicConstraint right) {
            this.left = left; this.right = right;
        }
    }

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

        /**
         * Checks if this equality is false.
         * 
         * @return true if this equality is definitely false; otherwise, false
         */
        public boolean isFalse() {
            if (leftHandSide instanceof Bottom || rightHandSide instanceof Bottom)
                return true;
            if (leftHandSide.isGround() && rightHandSide.isGround()) {
                return !leftHandSide.equals(rightHandSide);
            }
            if (!(leftHandSide instanceof Sorted) || !(rightHandSide instanceof Sorted)) {
                return false;
            }

            // TODO(AndreiS): treat HOLE more uniformly
            if (leftHandSide == Hole.HOLE && (rightHandSide instanceof Sorted)
                    && !definition.context().isSubsortedEq(((Sorted) rightHandSide).sort(), KSorts.KITEM)) {
                return true;
            }
            if (rightHandSide == Hole.HOLE && (leftHandSide instanceof Sorted)
                && !definition.context().isSubsortedEq(((Sorted) leftHandSide).sort(), KSorts.KITEM)) {
                return true;
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

        /**
         * Checks if this equality is true.
         * 
         * @return true if this equality is definitely true; otherwise, false
         */
        public boolean isTrue() {
            if (leftHandSide  instanceof Bottom || rightHandSide instanceof Bottom) return false;
            return leftHandSide.equals(rightHandSide);
        }

        /**
         * Checks if the truth value of this equality is unknown.
         * 
         * @return true if the truth value of this equality cannot be decided
         *         currently; otherwise, false
         */
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
        
        // TODO(YilongL): method hashCode needs to be overriden?

        @Override
        public String toString() {
            return leftHandSide + SEPARATOR + rightHandSide;
        }

    }

    public static final String SEPARATOR = " /\\ ";

    private static final Joiner joiner = Joiner.on(SEPARATOR);
    private static final Joiner.MapJoiner substitutionJoiner
            = joiner.withKeyValueSeparator(Equality.SEPARATOR);

    /**
     * Stores ordinary equalities in this symbolic constraint.
     * 
     * @see SymbolicConstraint#substitution
     */
    private final LinkedList<Equality> equalities = new LinkedList<Equality>();
    
    /**
     * Specifies if this symbolic constraint is in normal form.
     * <p>
     * <br>
     * A symbolic constraint is normal iff:
     * <li>no variable from the keys of {@code substitution} occurs in
     * {@code equalities};
     * <li>equalities between variables and terms are stored in
     * {@code substitution} rather than {@code equalities}.
     */
    private boolean isNormal;
    
    /**
     * Stores special equalities whose left-hand sides are just variables.
     * <p>
     * <br>
     * Invariant: {@code Variable}s on the left-hand sides do not occur in the
     * {@code Term}s on the right-hand sides.
     */
    private Map<Variable, Term> substitution = new HashMap<Variable, Term>();
    private TruthValue truthValue;
    private final TermContext context;
    private final Definition definition;
    private final SymbolicUnifier unifier;

    public SymbolicConstraint(SymbolicConstraint constraint, TermContext context) {
        this(context);
        substitution = new HashMap<>(constraint.substitution);
        addAll(constraint);
    }

    public SymbolicConstraint(TermContext context) {
        this.context = context;
        this.definition = context.definition();
        unifier = new SymbolicUnifier(this, context);
        truthValue = TruthValue.TRUE;
        isNormal = true;
    }
    
    /**
     * Adds a new equality to this symbolic constraint.
     * 
     * @param leftHandSide
     *            the left-hand side of the equality
     * @param rightHandSide
     *            the right-hand side of the equality
     * @return the truth value of this symbolic constraint after including the
     *         new equality
     */
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

    /**
     * Adds the side condition of a rule to this symbolic constraint. The side
     * condition is represented as a set of {@code Term}s that are expected to
     * be equal to {@code BoolToken#TRUE}.
     * 
     * @param condition
     *            the side condition
     * @return the truth value after including the side condition
     */
    public TruthValue addAll(Collection<Term> condition) {
        for (Term term : condition) {
            add(term, BoolToken.TRUE);
        }

        return truthValue;
    }

    /**
     * Adds all equalities in the given symbolic constraint to this one.
     * 
     * @param constraint
     *            the given symbolic constraint
     * @return the truth value after including the new equalities
     */
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

    /**
     * @return an unmodifiable view of the field {@code equalities}
     */
    public List<Equality> equalities() {
        normalize();
        return Collections.unmodifiableList(equalities);
    }

    /**
     * @return an unmodifiable view of the field {@code substitution}
     */
    public Map<Variable, Term> substitution() {
        normalize();
        return Collections.unmodifiableMap(substitution);
    }

    /**
     * Removes equalities between anonymous variables and terms.
     * <p>
     * <br>
     * TODO(YilongL): the following needs to be revised to be precise<br>
     * Anonymous variables are generated for doing unification; they are no
     * longer needed at the end of a rewrite step.
     */
    public void eliminateAnonymousVariables() {
        for (Iterator<Variable> iterator = substitution.keySet().iterator(); iterator.hasNext();) {
            Variable variable = iterator.next();
            if (variable.isAnonymous()) {
                iterator.remove();
            }
        }
    }

    /**
     * (Re-)computes the truth value of this symbolic constraint.
     * @return the truth value
     */
    public TruthValue getTruthValue() {
        normalize();
        return truthValue;
    }

    public boolean implies(SymbolicConstraint constraint) {
        LinkedList<Implication> implications = new LinkedList<>();
        implications.add(new Implication(this, constraint));
        while (!implications.isEmpty()) {
            Implication implication = implications.remove();

            SymbolicConstraint left = implication.left;
            SymbolicConstraint right = implication.right;
            if (left.isFalse()) continue;

            right = left.simplifyConstraint(right);
            if (right.isTrue() || right.equalities().isEmpty()) {
                if (DEBUG) {
                    System.out.println("Implication proved by simplification");
                }
                continue;
            }
            IfThenElseFinder ifThenElseFinder = new IfThenElseFinder(context);
            right.accept(ifThenElseFinder);
            if (!ifThenElseFinder.result.isEmpty()) {
                KItem ite = ifThenElseFinder.result.get(0);
                Term condition = ite.kList().get(0);
                if (DEBUG) {
                    System.out.println("Split on " + condition);
                }
                SymbolicConstraint left1 = new SymbolicConstraint(left, context);
                left1.add(condition, BoolToken.TRUE);
                implications.add(new Implication(left1, new SymbolicConstraint(right,context)));
                SymbolicConstraint left2 = new SymbolicConstraint(left, context);
                left2.add(condition, BoolToken.FALSE);
                implications.add(new Implication(left2, new SymbolicConstraint(right,context)));
                continue;
            }
//            if (DEBUG) {
//                System.out.println("After simplification, verifying whether\n\t" + left.toString() + "\nimplies\n\t" + right.toString());
//            }
            if (!impliesSMT(left,right)) {
                if (DEBUG) {
                    System.out.println("Failure!");
                }
                return false;
            } else {
                if (DEBUG) {
                    System.out.println("Proved!");
                }
            }
        }
       return true;
    }


    private static boolean impliesSMT(SymbolicConstraint left, SymbolicConstraint right) {
        boolean result = false;
        if (K.smt.equals("gappa")) {

            GappaPrinter.GappaPrintResult premises = GappaPrinter.toGappa(left);
            String gterm1 = premises.result;
            GappaPrinter.GappaPrintResult conclusion = GappaPrinter.toGappa(right);
            if (conclusion.exception != null) {
                System.err.print(conclusion.exception.getMessage());
                System.err.println(" Cannot prove the full implication!");
                return false;
            }
            String gterm2 = conclusion.result;
            String input = "";
            Set<String> variables = new HashSet<>();
            variables.addAll(premises.variables);
            variables.addAll(conclusion.variables);
            for (String variable : variables) {
                GappaServer.addVariable(variable);
            }
            if (!gterm1.equals("")) input += "(" + gterm1 + ") -> ";
            input += "(" + gterm2 + ")";
            if (DEBUG) {
                System.out.println("Verifying " + input);
            }
            if (GappaServer.proveTrue(input))
                result = true;

//            System.out.println(constraint);
        } else if (K.smt.equals("z3")) {
            Set<Variable> rightHandSideVariables = new HashSet<Variable>(right.variableSet());
            rightHandSideVariables.removeAll(left.variableSet());

            try {
                com.microsoft.z3.Context context = Z3Wrapper.newContext();
                KILtoZ3 transformer = new KILtoZ3(rightHandSideVariables, context);

                Solver solver = context.MkSolver();

                for (Equality equality : left.equalities) {
                    solver.Assert(context.MkEq(
                            ((Z3Term) equality.leftHandSide.accept(transformer)).expression(),
                            ((Z3Term) equality.rightHandSide.accept(transformer)).expression()));
                }

                //BoolExpr[] inequalities = new BoolExpr[constraint.equalities.size() + constraint.substitution.size()];
                BoolExpr[] inequalities = new BoolExpr[right.equalities.size()];
                int i = 0;
                for (Equality equality : right.equalities) {
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
        return  result;
    }

    private SymbolicConstraint simplifyConstraint(SymbolicConstraint constraint) {
        constraint.normalize();
        List<Equality> equalities = new LinkedList<>(constraint.equalities());
        ListIterator<Equality> listIterator = equalities.listIterator();
        while (listIterator.hasNext()) {
            Equality e2 = listIterator.next();
            for (Equality e1 : equalities()) {
                if (e2.equals(e1)) {
                    listIterator.remove();
                    break;
                }
            }
        }
        Map<Term, Term> substitution = new HashMap<>();
        for (Equality e1:equalities()) {
            if (e1.rightHandSide.isGround()) {
                substitution.put(e1.leftHandSide,e1.rightHandSide);
            }
            if (e1.leftHandSide.isGround()) {
                substitution.put(e1.rightHandSide,e1.leftHandSide);
            }
        }
        constraint = (SymbolicConstraint) substituteTerms(constraint, substitution);
        constraint.renormalize();
        constraint.simplify();
        return constraint;
    }

    private JavaSymbolicObject substituteTerms(JavaSymbolicObject constraint, Map<Term, Term> substitution) {
        return (JavaSymbolicObject) constraint.accept(new TermSubstitutionTransformer(substitution,context));
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

    /**
     * TODO(YilongL):Gets solutions to this symbolic constraint?
     * @return
     */
    public Collection<SymbolicConstraint> getMultiConstraints() {
        if (!unifier.multiConstraints.isEmpty()) {
            assert unifier.multiConstraints.size() == 1;

            List<SymbolicConstraint> multiConstraints = new ArrayList<SymbolicConstraint>();
            for (SymbolicConstraint constraint : unifier.multiConstraints.iterator().next()) {
                constraint.addAll(this);
                constraint.simplify();
                multiConstraints.add(constraint);
            }
            return multiConstraints;
        } else {
            return Collections.singletonList(this);
        }
    }

    /**
     * Simplifies this symbolic constraint as much as possible. Decomposes large
     * equalities into small ones using unification.
     * 
     * @return the truth value of this symbolic constraint after simplification
     */
    public TruthValue simplify() {
        boolean change; // specifies if the equalities have been further
                         // simplified in the last iteration
        
        label: do {
            change = false;
            normalize();

            for (int i = 0; i < equalities.size(); ++i) {
                Equality equality = equalities.get(i);
                if (!equality.leftHandSide.isSymbolic() && !equality.rightHandSide.isSymbolic()) {
                    // if both sides of the equality could be further
                    // decomposed, unify them
                    equalities.remove(i);
                    i--;
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

    /**
     * Converts this symbolic constraint back to normal form.
     */
    private void normalize() {
        if (isNormal) {
            return;
        }
        renormalize();
    }
    private void renormalize() {
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

    /**
     * Composes two substitutions. The first substitution holds the result
     * composition.
     * 
     * @param subst1
     *            the first substitution
     * @param subst2
     *            the second substitution
     * @param context
     *            the term context
     */
    @SuppressWarnings("unchecked")
    public static void compose(
            Map<Variable, Term> subst1,
            Map<Variable, Term> subst2,
            TermContext context) {
        Map.Entry<Variable, Term>[] entries = subst1.entrySet().toArray(new Map.Entry[subst1.size()]);
        for (Map.Entry<Variable, Term> entry : entries) {
            Term term = entry.getValue().substitute(subst2, context);
            if (term != entry.getValue()) {
                subst1.put(entry.getKey(), term);
            }
        }
        // TODO(YilongL): not done yet; need to merge two subst's and makes sure
        // the invariant
        // holds(http://www.mathcs.duq.edu/simon/Fall04/notes-7-4/node4.html)
    }

    /**
     * Renames the given set of variables and returns the new names. Updates
     * their occurrences in this symbolic constraint accordingly.
     * 
     * @param variableSet
     *            the set of variables to be renamed
     * @return a mapping from the old names to the new ones
     */
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

    /**
     * Finds an innermost occurrence of the #if_#then_#else_#fi function.
     *
     * @author Traian
     */
    private class IfThenElseFinder extends PrePostVisitor {
        final List<KItem> result;
        private String IF_THEN_ELSE_LABEL="'#if_#then_#else_#fi";

        public IfThenElseFinder(TermContext context) {
            result = new ArrayList<>();
            preVisitor.addVisitor(new LocalVisitor() {
                @Override
                protected void visit(JavaSymbolicObject object) {
                    proceed = result.isEmpty();
                }
            });
            postVisitor.addVisitor(new LocalVisitor(){
                @Override
                public void visit(KItem kItem) {
                    if (!result.isEmpty()) return;
                    if (kItem.kLabel() instanceof KLabelConstant &&
                            ((KLabelConstant) kItem.kLabel()).label().equals(IF_THEN_ELSE_LABEL)) {
                        result.add(kItem);
                    }
                }
            });
        }
    }
}

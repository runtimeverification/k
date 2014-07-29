// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.DataStructureLookupOrChoice;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.kil.Z3Term;
import org.kframework.backend.java.util.GappaPrinter;
import org.kframework.backend.java.util.GappaServer;
import org.kframework.backend.java.util.Utils;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.kil.ASTNode;
import org.kframework.utils.options.SMTSolver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Joiner;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;

/**
 * A conjunction of equalities between terms (with variables).
 *
 * @author AndreiS
 */
public class SymbolicConstraint extends JavaSymbolicObject {
    public static class Data {
        /**
         * Stores ordinary equalities in this symbolic constraint.
         * <p>
         * Invariant: there can be at most one equality in this list whose result is
         * {@code TruthValue#FALSE} (since this symbolic constraint becomes
         * {@code TruthValue#FALSE} then); the {@link TruthValue} of the rest
         * equalities must be {@code TruthValue#UNKNOWN}.
         * <p>
         * In order to preserve this invariant, whenever an equality has been
         * changed (i.e., substitution and/or evaluation), the truth value of this
         * equality shall be re-checked.
         *
         * @see SymbolicConstraint#data.substitution
         */
        public LinkedList<Equality> equalities;
        /**
         * Specifies if this symbolic constraint is in normal form.
         * <p>
         * A symbolic constraint is normal iff:
         * <li>no variable from the keys of {@code substitution} occurs in
         * {@code equalities};
         * <li>equalities between variables and terms are stored in
         * {@code substitution} rather than {@code equalities}.
         */
        public boolean isNormal;
        /**
         * Stores special equalities whose left-hand sides are just variables.
         * <p>
         * Invariants:
         * <li> {@code Variable}s on the left-hand sides do not occur in the
         * {@code Term}s on the right-hand sides;
         * <li>the invariant of {@code SymbolicConstraint#equalities} also applies
         * here.
         *
         * @see SymbolicConstraint#data.equalities
         */
        public Map<Variable, Term> substitution;
        public TruthValue truthValue;
        /**
         * Stores the minimal equality causing this constraint to become false.
         * It is null is this constraint is not false.
         */
        public Equality falsifyingEquality;

        public SymbolicUnifier.Data unifierData;

        public Data(LinkedList<Equality> equalities, Map<Variable, Term> substitution,
                TruthValue truthValue, boolean isNormal, SymbolicUnifier.Data unifierData) {
            this.equalities = equalities;
            this.substitution = substitution;
            this.truthValue = truthValue;
            this.isNormal = isNormal;
            this.unifierData = unifierData;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((equalities == null) ? 0 : equalities.hashCode());
            result = prime * result + ((substitution == null) ? 0 : substitution.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Data other = (Data) obj;
            if (equalities == null) {
                if (other.equalities != null)
                    return false;
            } else if (!equalities.equals(other.equalities))
                return false;
            if (substitution == null) {
                if (other.substitution != null)
                    return false;
            } else if (!substitution.equals(other.substitution))
                return false;
            return true;
        }
    }

    private static final boolean DEBUG = true;

    public void orientSubstitution(Set<Variable> variables) {
        Map<Variable, Term> newSubstitution = new HashMap<>();
        if (data.substitution.keySet().containsAll(variables)) {
            /* avoid setting isNormal to false */
            return;
        }

        /* compute the preimages of each variable in the codomain of the substitution */
        Map<Variable, Set<Variable>> preimages = new HashMap<Variable, Set<Variable>>();
        for (Map.Entry<Variable, Term> entry : data.substitution.entrySet()) {
            if (entry.getValue() instanceof Variable) {
                Variable rhs = (Variable) entry.getValue();
                if (preimages.get(rhs) == null) {
                    preimages.put(rhs, new HashSet<Variable>());
                }
                preimages.get(rhs).add(entry.getKey());
            }
        }

        Set<Variable> substitutionToRemove = new HashSet<Variable>();
        for (Map.Entry<Variable, Term> entry : data.substitution.entrySet()) {
            Variable lhs = entry.getKey();
            Term rhs = entry.getValue();
            if (variables.contains(rhs) && !newSubstitution.containsKey(rhs)) {
                /*
                 * case 1: both lhs & rhs are required to be on the LHS
                 *      before              after
                 *     lhs  ---> rhs        lhs  ---> lhs' (added to newSubstitution)
                 *     lhs' ---> rhs  ==>   rhs  ---> lhs' (added to newSubstitution)
                 *     lhs''---> rhs        lhs''---> rhs  (rhs will get substituted later)
                 */
                if (variables.contains(lhs)) {
                    /*
                     * preimagesOfRHS is guaranteed to contain all variables
                     * that are constrained to be equal to the variable rhs
                     * because rhs cannot appear on the LHS of the substitution
                     */
                    Set<Variable> preimagesOfRHS = new HashSet<Variable>(preimages.get(rhs));
                    preimagesOfRHS.removeAll(variables);
                    if (preimagesOfRHS.isEmpty()) {
                        throw new RuntimeException("Orientation failed");
                    }
                    Variable newRHS = preimagesOfRHS.iterator().next();
                    newSubstitution.put(lhs, newRHS);
                    newSubstitution.put((Variable) rhs, newRHS);
                    substitutionToRemove.add(lhs);
                    substitutionToRemove.add(newRHS);
                }
                /*
                 * case 2: rhs is required to be on the LHS but not lhs
                 *      before              after
                 *     lhs ---> rhs  ==>   rhs  ---> lhs (added to newSubstitution)
                 */
                else {
                    newSubstitution.put((Variable) rhs, lhs);
                    substitutionToRemove.add(lhs);
                }
            }
        }

        Map<Variable, Term> result = new HashMap<>();
        for (Variable var : substitutionToRemove)
            data.substitution.remove(var);
        for (Map.Entry<Variable, Term> entry : newSubstitution.entrySet()) {
            data.substitution.remove(entry.getValue());
            // TODO(YilongL): why not evaluate entry.getValue() after the substitution?
            result.put(entry.getKey(), entry.getValue().substituteWithBinders(newSubstitution, context));
        }
        for (Map.Entry<Variable, Term> entry : data.substitution.entrySet()) {
            result.put(entry.getKey(), entry.getValue().substituteWithBinders(newSubstitution, context));
        }

        data.substitution.clear();
        for (Map.Entry<Variable, Term> subst : result.entrySet()) {
            checkTruthValBeforePutIntoConstraint(subst.getKey(), subst.getValue(), true);
        }

        /*
         * after re-orientation, the {@code equalities} may contain variables on
         * the LHS's of the {@code substitution}
         */
        data.isNormal = false;
    }

    public Equality falsifyingEquality() {
        return data.falsifyingEquality;
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

        private final Term leftHandSide;
        private final Term rightHandSide;

        private Equality(Term leftHandSide, Term rightHandSide) {
            if (leftHandSide instanceof Bottom) rightHandSide = leftHandSide;
            if (rightHandSide instanceof Bottom) leftHandSide = rightHandSide;

            assert checkKindMisMatch(leftHandSide, rightHandSide):
                    "kind mismatch between "
                    + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                    + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

            if (leftHandSide.kind() == Kind.K || leftHandSide.kind() == Kind.KLIST) {
                leftHandSide = KCollection.downKind(leftHandSide);
            }
            if (leftHandSide.kind() == Kind.CELL_COLLECTION) {
                leftHandSide = CellCollection.downKind(leftHandSide);
            }
            if (rightHandSide.kind() == Kind.K || rightHandSide.kind() == Kind.KLIST) {
                rightHandSide = KCollection.downKind(rightHandSide);
            }
            if (rightHandSide.kind() == Kind.CELL_COLLECTION) {
                rightHandSide = CellCollection.downKind(rightHandSide);
            }

            // YilongL: we can not do the following here for now because builtin
            // lookups maynot have the correct, or concrete, kind/sort
            // e.g., currently, node ListLookup (always) has Kind.K
            // Besides, it is better leave the complex decision in one place,
            // which is the SymbolicUnifier, the assertion at the beginning is
            // merely a simple sanity check
            // assert leftHandSide.kind() == rightHandSide.kind();

            this.leftHandSide = leftHandSide;
            this.rightHandSide = rightHandSide;
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
            if (leftHandSide instanceof Bottom || rightHandSide instanceof Bottom) {
                return true;
            }
            /* both leftHandSide & rightHandSide must have been evaluated before
             * this method is invoked */
            if (leftHandSide.isGround() && rightHandSide.isGround()) {
                return !leftHandSide.equals(rightHandSide);
            }

            if (leftHandSide instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) leftHandSide).matchConcreteSize(rightHandSide)) {
                return true;
            } else if (rightHandSide instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) rightHandSide).matchConcreteSize(leftHandSide)) {
                return true;
            }

            if (!termContext().definition().context().javaExecutionOptions.generateTests) {
                if (leftHandSide.isExactSort() && rightHandSide.isExactSort()) {
                    return !leftHandSide.sort().equals(rightHandSide.sort());
                } else if (leftHandSide.isExactSort()) {
                    return !definition.subsorts().isSubsortedEq(
                            rightHandSide.sort(),
                            leftHandSide.sort());
                } else if (rightHandSide.isExactSort()) {
                    return !definition.subsorts().isSubsortedEq(
                            leftHandSide.sort(),
                            rightHandSide.sort());
                } else {
                    return !definition.subsorts().hasCommonSubsort(
                            leftHandSide.sort(),
                            rightHandSide.sort());
                }
            } else {
                if (leftHandSide instanceof KItem && ((KItem) leftHandSide).kLabel() instanceof KLabel
                        && ((KLabel) ((KItem) leftHandSide).kLabel()).isConstructor()) {
                    for (Sort pms : ((KItem) leftHandSide).possibleMinimalSorts()) {
                        if (definition.subsorts().isSubsortedEq(rightHandSide.sort(), pms)) {
                            return false;
                        }
                    }
                    return true;
                } else if (rightHandSide instanceof KItem && ((KItem) rightHandSide).kLabel() instanceof KLabel
                        && ((KLabel) ((KItem) rightHandSide).kLabel()).isConstructor()) {
                    for (Sort pms : ((KItem) rightHandSide).possibleMinimalSorts()) {
                        if (definition.subsorts().isSubsortedEq(leftHandSide.sort(), pms)) {
                            return false;
                        }
                    }
                    return true;
                } else {
                    return definition.subsorts().hasCommonSubsort(
                        (leftHandSide).sort(),
                        (rightHandSide).sort());
                }
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

        /**
         * Returns an {@code Equality} obtained by applying the {@code substitution} on
         * {@code this} equality.
         *
         * @param substitution
         *            the specified substitution map
         */
        private Equality substitute(Map<Variable, ? extends Term> substitution) {
            Term returnLeftHandSide = leftHandSide.substituteWithBinders(substitution, context);
            Term returnRightHandSide = rightHandSide.substituteWithBinders(substitution, context);
            if (returnLeftHandSide != leftHandSide || returnRightHandSide != rightHandSide) {
                return new Equality(returnLeftHandSide, returnRightHandSide);
            } else {
                return this;
            }
        }

        /**
         * Returns an {@code Equality} obtained by applying the {@code substitution} on
         * {@code this} equality and then evaluating pending functions.
         *
         * @param substitution
         *            the specified substitution map
         */
        private Equality substituteAndEvaluate(Map<Variable, ? extends Term> substitution) {
            Term returnLeftHandSide = leftHandSide.substituteAndEvaluate(substitution, context);
            Term returnRightHandSide = rightHandSide.substituteAndEvaluate(substitution, context);
            if (returnLeftHandSide != leftHandSide || returnRightHandSide != rightHandSide) {
                return new Equality(returnLeftHandSide, returnRightHandSide);
            } else {
                return this;
            }
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
            int hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + leftHandSide.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + rightHandSide.hashCode();
            return hashCode;
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

    private final ArrayList<Equality> equalityBuffer = new ArrayList<Equality>();

    private boolean simplifyingEqualities = false;

    public final Data data;

    private final TermContext context;
    private final Definition definition;

    /**
     * The symbolic unifier associated with this constraint. There is an
     * one-to-one relationship between unifiers and constraints.
     */
    private final SymbolicUnifier unifier;

    public SymbolicConstraint(Data data, TermContext context) {
        this.data = data;
        this.context = context;
        this.definition = context.definition();
        this.unifier = new SymbolicUnifier(this, data.unifierData, context);
    }

    public SymbolicConstraint(SymbolicConstraint constraint, TermContext context) {
        this(context);
        data.substitution.putAll(constraint.data.substitution);
        addAll(constraint);
    }

    public SymbolicConstraint(TermContext context) {
        this(new Data(
                new LinkedList<Equality>(), new HashMap<Variable, Term>(), TruthValue.TRUE, true,
                new SymbolicUnifier.Data()),
                context);
    }

    public TermContext termContext() {
        return context;
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
        assert checkKindMisMatch(leftHandSide, rightHandSide):
                "kind mismatch between "
                + leftHandSide + " (instanceof " + leftHandSide.getClass() + ")" + " and "
                + rightHandSide + " (instanceof " + rightHandSide.getClass() + ")";

        if (simplifyingEqualities) {
            Equality equality = new Equality(leftHandSide, rightHandSide);
            if (equality.isFalse()) {
                falsify(equality);
            } else if (equality.isUnknown()) {
                equalityBuffer.add(equality);
                data.isNormal = false;
            }
        } else {
            simplify(); // YilongL: normalize() is not enough
            leftHandSide = leftHandSide.substituteAndEvaluate(data.substitution, context);
            rightHandSide = rightHandSide.substituteAndEvaluate(data.substitution, context);

            checkTruthValBeforePutIntoConstraint(leftHandSide, rightHandSide, false);
        }
        return data.truthValue;
    }

    private boolean checkKindMisMatch(Term leftHandSide, Term rightHandSide) {
        return leftHandSide.kind() == rightHandSide.kind()
                || ((leftHandSide.kind() == Kind.KITEM
                        || leftHandSide.kind() == Kind.K || leftHandSide.kind() == Kind.KLIST) && (rightHandSide
                        .kind() == Kind.KITEM || rightHandSide.kind() == Kind.K || rightHandSide
                        .kind() == Kind.KLIST))
                || ((leftHandSide.kind() == Kind.CELL || leftHandSide.kind() == Kind.CELL_COLLECTION) && (rightHandSide
                        .kind() == Kind.CELL || rightHandSide.kind() == Kind.CELL_COLLECTION));
    }

    /**
     * Private helper method that checks the truth value of a specified equality
     * and put it into the equality list or substitution map maintained by this
     * symbolic constraint properly.
     *
     * @param leftHandSide
     *            the left-hand side of the specified equality
     * @param rightHandSide
     *            the right-hand side of the specified equality
     * @param putInSubst
     *            specifies whether the equality can be safely added to the
     *            substitution map of this symbolic constraint
     */
    private void checkTruthValBeforePutIntoConstraint(Term leftHandSide, Term rightHandSide, boolean putInSubst) {
        if (data.truthValue == TruthValue.FALSE) {
            return;
        }

        // assume the truthValue to be TRUE or UNKNOWN from now on
        Equality equality = this.new Equality(leftHandSide, rightHandSide);
        if (equality.isUnknown()){
            if (putInSubst) {
                Term origVal = data.substitution.put((Variable) leftHandSide, rightHandSide);
                if (origVal == null) {
                    data.isNormal = false;
                }
            } else {
                data.equalities.add(equality);
                data.isNormal = false;
            }
            data.truthValue = TruthValue.UNKNOWN;
        } else if (equality.isFalse()) {
            if (putInSubst) {
                data.substitution.put((Variable) leftHandSide, rightHandSide);
            } else {
                data.equalities.add(equality);
            }
            falsify(equality);
        }
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

        return data.truthValue;
    }

    /**
     * Adds all equalities in the given symbolic constraint to this one.
     *
     * @param constraint
     *            the given symbolic constraint
     * @return the truth value after including the new equalities
     */
    public TruthValue addAll(SymbolicConstraint constraint) {
        for (Map.Entry<Variable, Term> entry : constraint.data.substitution.entrySet()) {
            add(entry.getValue(), entry.getKey());
        }

        for (Equality equality : constraint.data.equalities) {
            add(equality.leftHandSide, equality.rightHandSide);
        }

        return data.truthValue;
    }

    public boolean checkUnsat() {
        if (termContext().definition().context().smtOptions.smt != SMTSolver.Z3) {
            return false;
        }

        normalize();
        if (isSubstitution()) {
            return false;
        }

        Boolean result = false;
        try {
            com.microsoft.z3.Context context = Z3Wrapper.newContext();
            KILtoZ3 transformer = new KILtoZ3(Collections.<Variable>emptySet(), context);
            Solver solver = context.MkSolver();
            for (Equality equality : data.equalities) {
                try {
                    solver.Assert(context.MkEq(
                            ((Z3Term) equality.leftHandSide.accept(transformer)).expression(),
                            ((Z3Term) equality.rightHandSide.accept(transformer)).expression()));
                } catch (UnsupportedOperationException e) {
                    /* it is sound to skip the equalities that cannot be translated */
                    // TODO(AndreiS): fix this translation and the exceptions
                    e.printStackTrace();
                }
                result = solver.Check() == Status.UNSATISFIABLE;
                context.Dispose();
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
        }
        return result;
    }

    /**
     * @return an unmodifiable view of the field {@code equalities}
     */
    public List<Equality> equalities() {
        normalize();
        return Collections.unmodifiableList(data.equalities);
    }

    /**
     * @return an unmodifiable view of the field {@code substitution}
     */
    public Map<Variable, Term> substitution() {
        normalize();
        return Collections.unmodifiableMap(data.substitution);
    }

    /**
     * Garbage collect useless bindings. This method should be called after
     * applying the substitution to the RHS of a rule. It then removes all
     * bindings of anonymous variables.
     */
    public void eliminateAnonymousVariables() {
        for (Iterator<Variable> iterator = data.substitution.keySet().iterator(); iterator.hasNext();) {
            Variable variable = iterator.next();
            if (variable.isAnonymous()) {
                iterator.remove();
            }
        }

        /* reset this symbolic constraint to be true when it becomes empty */
        if (data.equalities.isEmpty() && data.substitution.isEmpty()) {
            data.truthValue = TruthValue.TRUE;
        }
    }

    /**
     * (Re-)computes the truth value of this symbolic constraint.
     * @return the truth value
     */
    public TruthValue getTruthValue() {
        normalize();
        return data.truthValue;
    }

    public boolean implies(SymbolicConstraint constraint) {
        LinkedList<Implication> implications = new LinkedList<>();
        implications.add(new Implication(this, constraint));
        while (!implications.isEmpty()) {
            Implication implication = implications.remove();

            SymbolicConstraint left = implication.left;
            SymbolicConstraint right = implication.right;
            if (left.isFalse()) continue;

            if (DEBUG) {
                System.out.println("Attempting to prove: \n\t" + left + "\n  implies \n\t" + right);
            }

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
                // TODO (AndreiS): handle KList variables
                Term condition = ((KList) ite.kList()).get(0);
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
        assert left.termContext().definition().context() == right.termContext().definition().context();
        if (left.termContext().definition().context().smtOptions.smt == SMTSolver.GAPPA) {

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
        } else if (left.termContext().definition().context().smtOptions.smt == SMTSolver.Z3) {
            Set<Variable> rightHandSideVariables = new HashSet<Variable>(right.variableSet());
            rightHandSideVariables.removeAll(left.variableSet());

            try {
                com.microsoft.z3.Context context = Z3Wrapper.newContext();
                KILtoZ3 transformer = new KILtoZ3(rightHandSideVariables, context);

                Solver solver = context.MkSolver();

                for (Equality equality : left.data.equalities) {
                    solver.Assert(context.MkEq(
                            ((Z3Term) equality.leftHandSide.accept(transformer)).expression(),
                            ((Z3Term) equality.rightHandSide.accept(transformer)).expression()));
                }

                //BoolExpr[] inequalities = new BoolExpr[constraint.equalities.size() + constraint.substitution.size()];
                BoolExpr[] inequalities = new BoolExpr[right.data.equalities.size()];
                int i = 0;
                for (Equality equality : right.data.equalities) {
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

                com.microsoft.z3.Sort[] variableSorts = new com.microsoft.z3.Sort[rightHandSideVariables.size()];
                Symbol[] variableNames = new Symbol[rightHandSideVariables.size()];
                i = 0;
                for (Variable variable : rightHandSideVariables) {
                    if (variable.sort().equals(BoolToken.SORT)) {
                        variableSorts[i] = context.MkBoolSort();
                    } else if (variable.sort().equals(IntToken.SORT)) {
                        variableSorts[i] = context.MkIntSort();
                    //} else if (variable.sort().equals(BitVector.SORT_NAME)) {
                    //    variableSorts[i] = context.MkBitVecSort(32);
                    // TODO(AndreiS): need support for parametric type MInt{32}, in order to
                    // translate to SMT
                    } else {
                        throw new UnsupportedOperationException(
                                "unexpected variable sort " + variable.sort());
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
            } catch (UnsupportedOperationException | Z3Exception e) {
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
        return data.truthValue == TruthValue.FALSE;
    }

    public boolean isTrue() {
        normalize();
        return data.truthValue == TruthValue.TRUE;
    }

    public boolean isSubstitution() {
        normalize();
        return data.equalities.isEmpty() && unifier.data.multiConstraints.isEmpty();
    }

    public boolean isUnknown() {
        normalize();
        return data.truthValue == TruthValue.UNKNOWN;
    }

    /**
     * Sets this constraint to be false, and record a minimal equality that makes it false.
     * @param equality
     */
    private void falsify(Equality equality) {
        // TODO(AndreiS): this assertion should not fail
        // assert truthValue == TruthValue.TRUE || truthValue == TruthValue.UNKNOWN;
        data.truthValue = TruthValue.FALSE;
        data.falsifyingEquality = equality;
    }

    /**
     * TODO(YilongL):Gets solutions to this symbolic constraint?
     * @return
     */
    public Collection<SymbolicConstraint> getMultiConstraints() {
        if (!unifier.data.multiConstraints.isEmpty()) {
            assert unifier.data.multiConstraints.size() <= 2;

            List<SymbolicConstraint> multiConstraints = new ArrayList<SymbolicConstraint>();
            Iterator<Collection<SymbolicConstraint>> iterator = unifier.multiConstraints().iterator();
            if (unifier.data.multiConstraints.size() == 1) {
                for (SymbolicConstraint constraint : iterator.next()) {
                    constraint.addAll(this);
                    constraint.simplify();
                    multiConstraints.add(constraint);
                }
            } else {
                Collection<SymbolicConstraint> constraints = iterator.next();
                Collection<SymbolicConstraint> otherConstraints = iterator.next();
                for (SymbolicConstraint cnstr1 : constraints) {
                    for (SymbolicConstraint cnstr2 : otherConstraints) {
                        SymbolicConstraint constraint = new SymbolicConstraint(
                                this, context);
                        constraint.addAll(cnstr1);
                        constraint.addAll(cnstr2);
                        constraint.simplify();
                        multiConstraints.add(constraint);
                    }
                }
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
        if (data.truthValue == TruthValue.FALSE) {
            return data.truthValue;
        }

        boolean change; // specifies if the equalities have been further
                         // simplified in the last iteration

        label: do {
            change = false;
            normalize();

            simplifyingEqualities = true;
            for (Iterator<Equality> iterator = data.equalities.iterator(); iterator.hasNext();) {
                Equality equality = iterator.next();
                if (!equality.leftHandSide.isSymbolic() && !equality.rightHandSide.isSymbolic()) {
                    // if both sides of the equality could be further
                    // decomposed, discharge the equality
                    iterator.remove();
                    if (!unifier.unify(equality)) {
                        falsify(new Equality(
                                unifier.unificationFailureLeftHandSide(),
                                unifier.unificationFailureRightHandSide()));
                        simplifyingEqualities = false;
                        break label;
                    }

                    change = true;
                }
            }

            simplifyingEqualities = false;
        } while (change);

        return data.truthValue;
    }

    /**
     * Recursive invocations of {@code SymbolicConstraint#normalize()} may occur
     * (if not handled properly) since the method {@code Term#evaluate} is
     * called during normalization process.
     */
    private boolean recursiveNormalize = false;

    /**
     * Normalizes the symbolic constraint.
     */
    private void normalize() {
        assert !simplifyingEqualities : "Do not modify the equalities when they are being simplified";

        if (data.isNormal) {
            return;
        }

        assert !recursiveNormalize : "recursive normalization shall not happen";
        recursiveNormalize = true;
        renormalize();

        /* reset this symbolic constraint to be true when it becomes empty */
        if (data.equalities.isEmpty() && data.substitution.isEmpty()) {
            data.truthValue = TruthValue.TRUE;
        }
        recursiveNormalize = false;
    }

    private void renormalize() {
        data.isNormal = true;
        data.equalities.addAll(equalityBuffer);
        equalityBuffer.clear();

        List<Integer> equalitiesToRemove = new ArrayList<>();
        for (int i = 0; i < data.equalities.size(); ++i) {
            // YilongL: no need to evaluate after substitution because the LHS
            // of the rule and the subject term should have no function symbol
            // inside; in other words, only side conditions need to be evaluated
            // and they should have been taken care of in method add(Term,Term)
            Equality equality = data.equalities.get(i).substitute(data.substitution);
            data.equalities.set(i, equality);

            if (equality.isTrue()) {
                equalitiesToRemove.add(i);
                continue;
            } else if (equality.isFalse()) {
                falsify(equality);
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

            /* cycle found */
            if (term.variableSet().contains(variable)) {
                continue;
            }

            equalitiesToRemove.add(i);

            Map<Variable, Term> tempSubst = Collections.singletonMap(variable, term);
            composeSubstitution(tempSubst, context, false);
            if (data.truthValue == TruthValue.FALSE) {
                return;
            }

            for (int j = 0; j < i; ++j) {
                /*
                 * Do not modify the previousEquality if it has been added to
                 * the HashSet equalitiesToRemove since this may result in
                 * inconsistent hashCodes in the HashSet; besides, there is no
                 * need to do so
                 */
                if (!equalitiesToRemove.contains(j)) {
                    Equality previousEquality = data.equalities.get(j).substituteAndEvaluate(tempSubst);
                    data.equalities.set(j, previousEquality);

                    if (previousEquality.isTrue()) {
                        equalitiesToRemove.add(j);
                    } else if (previousEquality.isFalse()) {
                        falsify(previousEquality);
                        return;
                    }
                }
            }
        }

        for (int i = equalitiesToRemove.size() - 1; i >= 0; --i) {
            data.equalities.remove((int) equalitiesToRemove.get(i));
        }
    }

    /**
     * Private helper method that composes a specified substitution map with the
     * substitution map of this symbolic constraint.
     *
     * @param substMap
     *            the specified substitution map
     * @param context
     *            the term context
     * @param mayInvalidateNormality
     *            whether this operation may cause
     *            {@link SymbolicConstraint#data.isNormal} to be {@code false}
     */
    private void composeSubstitution(Map<Variable, Term> substMap,
            TermContext context, boolean mayInvalidateNormality) {
        @SuppressWarnings("unchecked")
        Map.Entry<Variable, Term>[] entries = data.substitution.entrySet().toArray(new Map.Entry[data.substitution.size()]);
        for (Map.Entry<Variable, Term> subst : entries) {
            Term term = subst.getValue().substitute(substMap, context);
            if (term != subst.getValue()) {
                checkTruthValBeforePutIntoConstraint(subst.getKey(), term, true);
            }
        }

        // on composing two substitution maps:
        // http://www.mathcs.duq.edu/simon/Fall04/notes-7-4/node4.html
        Set<Variable> variables = new HashSet<Variable>(data.substitution.keySet());
        variables.retainAll(substMap.keySet());
        assert variables.isEmpty() :
            "There shall be no common variables in the two substitution maps to be composed.";
        data.substitution.putAll(substMap);

        if (mayInvalidateNormality) {
            data.isNormal = false;
        }
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
            if (data.substitution.get(variable) != null) {
                data.substitution.put(freshSubstitution.get(variable), data.substitution.remove(variable));
            }
        }

        /* rename in substitution values */
        for (Map.Entry<Variable, Term> entry : data.substitution.entrySet()) {
            entry.setValue(entry.getValue().substituteWithBinders(freshSubstitution, context));
        }

        for (int i = 0; i < data.equalities.size(); ++i) {
            data.equalities.set(i, data.equalities.get(i).substitute(freshSubstitution));
        }

        return freshSubstitution;
    }

    /**
     * Returns a new {@code SymbolicConstraint} instance obtained from this symbolic constraint
     * by applying substitution.
     */
    public SymbolicConstraint substituteWithBinders(Map<Variable, ? extends Term> substitution, TermContext context) {
        if (substitution.isEmpty()) {
            return this;
        }

        return (SymbolicConstraint) accept(new BinderSubstitutionTransformer(substitution, context));
    }

    /**
     * Returns a new {@code SymbolicConstraint} instance obtained from this symbolic constraint by
     * substituting variable with term.
     */
    public SymbolicConstraint substituteWithBinders(Variable variable, Term term, TermContext context) {
        return substituteWithBinders(Collections.singletonMap(variable, term), context);
    }

    /**
     * Checks if the rule application that produces this symbolic constraint is
     * driven by pattern matching instead of narrowing. This method should only
     * be called from the symbolic constraint that is returned by the method
     * {@code ConstrainedTerm#unify(ConstrainedTerm)}.
     *
     * @param pattern
     *            the pattern term, which is the left-hand side of a rule plus
     *            side conditions
     * @return {@code true} if the rule application is driven by pattern
     *         matching and all side conditions are successfully dissolved;
     *         otherwise, {@code false}
     */
    public boolean isMatching(ConstrainedTerm pattern) {
        orientSubstitution(pattern.variableSet());
        /*
         * YilongL: data structure lookups will change the variables on the LHS
         * of a rule, e.g.: "rule foo(M:Map X |-> Y, X) => 0" will be kompiled
         * into "rule foo(_,_)(_0:Map,, X) => 0 requires [] /\ _0:Map[X] = Y
         * ensures []". Therefore, we cannot write pattern.term().variableSet()
         * in the following check.
         */
        if (!isSubstitution() || !data.substitution.keySet().equals(pattern.variableSet())) {
            return false;
        }

        for (Map.Entry<Variable, Term> entry : data.substitution.entrySet()) {
            Sort sortOfPatVar = entry.getKey().sort();
            Term subst = entry.getValue();
            if (subst instanceof DataStructureLookupOrChoice) {
                return false;
            }
            Sort sortOfSubst = subst.sort();
            /* YilongL: There are three different cases:
             * 1) sortOfParVar >= sortOfSubst
             * 2) sortOfParVar < sortOfSubst
             * 3) there is no order between sortOfParVar & sortOfSubst
             * Only case 1) represents a pattern matching
             */
            if (!definition.subsorts().isSubsortedEq(sortOfPatVar, sortOfSubst)) {
                return false;
            }

            if (entry.getKey() instanceof ConcreteCollectionVariable
                    && !(entry.getValue() instanceof ConcreteCollectionVariable && ((ConcreteCollectionVariable) entry.getKey()).concreteCollectionSize() == ((ConcreteCollectionVariable) entry.getValue()).concreteCollectionSize())
                    && !(entry.getValue() instanceof org.kframework.backend.java.kil.Collection && !((org.kframework.backend.java.kil.Collection) entry.getValue()).hasFrame() && ((ConcreteCollectionVariable) entry.getKey()).concreteCollectionSize() == ((org.kframework.backend.java.kil.Collection) entry.getValue()).size())) {
                return false;
            }
        }
        return true;
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
        return data.equals(constraint.data);
    }

    @Override
    public int hashCode() {
        // TODO(YilongL): normalize and sort equalities?
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + data.hashCode();
        return hashCode;
    }

    @Override
    public String toString() {
        if (data.truthValue == TruthValue.TRUE) {
            return "true";
        }

        if (data.truthValue == TruthValue.FALSE) {
            return "false";
        }

        StringBuilder builder = new StringBuilder();
        builder = joiner.appendTo(builder, data.equalities);
        if (!(builder.length() == 0) && !data.substitution.isEmpty()) {
            builder.append(SEPARATOR);
        }
        builder = substitutionJoiner.appendTo(builder, data.substitution);
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
    protected <P, R, E extends Throwable> R accept(org.kframework.kil.visitors.Visitor<P, R, E> visitor, P p) throws E {
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

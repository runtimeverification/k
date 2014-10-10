// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.DataStructureLookupOrChoice;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.Utils;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.kil.ASTNode;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.SMTSolver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;
import com.google.common.collect.MapDifference;
import com.google.common.collect.Sets;
import com.google.common.collect.MapDifference.ValueDifference;
import com.google.common.collect.Maps;
import com.google.inject.Inject;
import com.google.inject.Provider;

/**
 * A conjunction of equalities between terms (with variables).
 *
 * @author AndreiS
 */
public class SymbolicConstraint extends JavaSymbolicObject {

    public static final String SEPARATOR = " /\\ ";

    private static final Joiner joiner = Joiner.on(SEPARATOR);
    private static final Joiner.MapJoiner substitutionJoiner
            = joiner.withKeyValueSeparator(Equality.SEPARATOR);

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
     * @see SymbolicConstraint#substitution
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
     * @see SymbolicConstraint#equalities
     */
    public LinkedHashMap<Variable, Term> substitution;

    public TruthValue truthValue;

    /**
     * Stores the minimal equality causing this constraint to become false.
     * It is null is this constraint is not false.
     */
    public Equality falsifyingEquality;

    private final ArrayList<Equality> equalityBuffer = Lists.newArrayList();

    private boolean equalitiesWriteProtected = false;

    private final TermContext context;

    /**
     * The symbolic unifier associated with this constraint. There is an
     * one-to-one relationship between unifiers and constraints.
     */
    private final SymbolicUnifier unifier;

    public void orientSubstitution(Set<Variable> variables) {
        Map<Variable, Term> newSubstitution = Maps.newLinkedHashMap();
        if (substitution.keySet().containsAll(variables)) {
            /* avoid setting isNormal to false */
            return;
        }

        /* compute the preimages of each variable in the codomain of the substitution */
        Map<Variable, Set<Variable>> preimages = Maps.newLinkedHashMap();
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            if (entry.getValue() instanceof Variable) {
                Variable rhs = (Variable) entry.getValue();
                if (preimages.get(rhs) == null) {
                    preimages.put(rhs, Sets.newLinkedHashSet());
                }
                preimages.get(rhs).add(entry.getKey());
            }
        }

        Set<Variable> substitutionToRemove = Sets.newLinkedHashSet();
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
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
                    Set<Variable> preimagesOfRHS = Sets.newLinkedHashSet(preimages.get(rhs));
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

        Map<Variable, Term> result = Maps.newLinkedHashMap();
        for (Variable var : substitutionToRemove)
            substitution.remove(var);
        for (Map.Entry<Variable, Term> entry : newSubstitution.entrySet()) {
            substitution.remove(entry.getValue());
            // TODO(YilongL): why not evaluate entry.getValue() after the substitution?
            result.put(entry.getKey(), entry.getValue().substituteWithBinders(newSubstitution, context));
        }
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            result.put(entry.getKey(), entry.getValue().substituteWithBinders(newSubstitution, context));
        }

        substitution.clear();
        for (Map.Entry<Variable, Term> subst : result.entrySet()) {
            checkTruthValBeforePutIntoConstraint(subst.getKey(), subst.getValue(), true);
        }

        /*
         * after re-orientation, the {@code equalities} may contain variables on
         * the LHS's of the {@code substitution}
         */
        isNormal = false;
    }

    public Equality falsifyingEquality() {
        return falsifyingEquality;
    }

    public static class SymbolicConstraintOperations {

        private final SMTOptions smtOptions;
        private final Z3Wrapper z3;
        private final GlobalOptions globalOptions;

        @Inject
        public SymbolicConstraintOperations(
                Provider<Definition> definitionProvider,
                SMTOptions smtOptions,
                Z3Wrapper z3,
                GlobalOptions globalOptions) {
            this.smtOptions = smtOptions;
            this.z3 = z3;
            this.globalOptions = globalOptions;
        }

        public boolean checkUnsat(SymbolicConstraint constraint) {
            if (smtOptions.smt != SMTSolver.Z3) {
                return false;
            }

            constraint.normalize();
            if (constraint.isSubstitution()) {
                return false;
            }

            boolean result = false;
            try {
                result = z3.checkQuery(
                        KILtoSMTLib.translateConstraint(constraint),
                        smtOptions.z3CnstrTimeout);
            } catch (UnsupportedOperationException e) {
                e.printStackTrace();
            }
            return result;
        }

        public boolean impliesSMT(SymbolicConstraint left,
                SymbolicConstraint right, Set<Variable> rightOnlyVariables) {
            boolean result = false;
            assert left.termContext().definition().context() == right.termContext().definition().context();
            if (smtOptions.smt == SMTSolver.Z3) {
                try {
                    result = z3.checkQuery(
                            KILtoSMTLib.translateImplication(left, right, rightOnlyVariables),
                            smtOptions.z3ImplTimeout);
                } catch (UnsupportedOperationException e) {
                    e.printStackTrace();
                }
            }
            return  result;
        }
    }

    public static SymbolicConstraint simplifiedConstraintFrom(TermContext context, Object... args) {
        SymbolicConstraint constraint = new SymbolicConstraint(context);
        constraint.addAll(args);
        constraint.simplify();
        return constraint;
    }

    public SymbolicConstraint(SymbolicConstraint constraint, TermContext context) {
        this(context);
        substitution.putAll(constraint.substitution);
        addAll(constraint);
    }

    public SymbolicConstraint(TermContext context) {
        substitution = Maps.newLinkedHashMap();
        equalities = Lists.newLinkedList();
        truthValue = TruthValue.TRUE;
        isNormal = true;
        unifier = new SymbolicUnifier(this, context);
        this.context = context;
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

        /* split andBool in multiple equalities */
        if (leftHandSide instanceof KItem && ((KItem) leftHandSide).kLabel().toString().equals("'_andBool_") && rightHandSide.equals(BoolToken.TRUE)) {
            add(((KList) ((KItem) leftHandSide).kList()).get(0), BoolToken.TRUE);
            add(((KList) ((KItem) leftHandSide).kList()).get(1), BoolToken.TRUE);
            return truthValue;
        }

        /* split andBool in multiple equalities */
        if (rightHandSide instanceof KItem && ((KItem) rightHandSide).kLabel().toString().equals("'_andBool_") && leftHandSide.equals(BoolToken.TRUE)) {
            add(((KList) ((KItem) rightHandSide).kList()).get(0), BoolToken.TRUE);
            add(((KList) ((KItem) rightHandSide).kList()).get(1), BoolToken.TRUE);
            return truthValue;
        }

        if (equalitiesWriteProtected) {
            Equality equality = new Equality(leftHandSide, rightHandSide, context);
            if (equality.truthValue() == TruthValue.FALSE) {
                falsify(equality);
            } else if (equality.truthValue() == TruthValue.UNKNOWN) {
                equalityBuffer.add(equality);
                isNormal = false;
            }
        } else {
            simplify(); // YilongL: normalize() is not enough
            leftHandSide = leftHandSide.substituteAndEvaluate(substitution, context);
            rightHandSide = rightHandSide.substituteAndEvaluate(substitution, context);

            checkTruthValBeforePutIntoConstraint(leftHandSide, rightHandSide, false);
        }
        return truthValue;
    }

    /**
     * Adds a new equality to this symbolic constraint.
     *
     * @param equality
     *            the new equality
     * @return the truth value of this symbolic constraint after including the
     *         new equality
     */
    public TruthValue add(Equality equality) {
        return add(equality.leftHandSide(), equality.rightHandSide());
    }

    boolean checkKindMisMatch(Term leftHandSide, Term rightHandSide) {
        return leftHandSide.kind() == rightHandSide.kind()
                || (leftHandSide.kind().isComputational() && rightHandSide.kind().isComputational())
                || (leftHandSide.kind().isStructural() && rightHandSide.kind().isStructural());
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
        if (truthValue == TruthValue.FALSE) {
            return;
        }

        // assume the truthValue to be TRUE or UNKNOWN from now on
        Equality equality = new Equality(leftHandSide, rightHandSide, context);
        if (equality.truthValue() == TruthValue.UNKNOWN){
            if (putInSubst) {
                Term origVal = substitution.put((Variable) leftHandSide, rightHandSide);
                if (origVal == null) {
                    isNormal = false;
                }
            } else {
                equalities.add(equality);
                isNormal = false;
            }
            truthValue = TruthValue.UNKNOWN;
        } else if (equality.truthValue() == TruthValue.FALSE) {
            if (putInSubst) {
                substitution.put((Variable) leftHandSide, rightHandSide);
            } else {
                equalities.add(equality);
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
        boolean eval = context.definition().context().krunOptions != null
                && context.definition().context().krunOptions.experimental.prove() != null;

        for (Term term : condition) {
            if (truthValue == TruthValue.FALSE) {
                break;
            }

            // TODO(AndreiS): remove this condition when function evaluation works properly
            if (eval) {
                add(term.evaluate(context), BoolToken.TRUE);
            } else {
                add(term, BoolToken.TRUE);

            }
        }

        return truthValue;
    }

    private TruthValue addAll(List<Equality> equalites) {
        for (Equality equality : equalites) {
            if (truthValue == TruthValue.FALSE) {
                break;
            }

            add(equality);
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
        addAll(constraint.substitution);
        for (Equality equality : constraint.equalities) {
            if (truthValue == TruthValue.FALSE) {
                break;
            }

            add(equality.leftHandSide(), equality.rightHandSide());
        }

        return truthValue;
    }

    /**
     * Adds all bindings in the given substitution map to this symbolic constraint.
     */
    public TruthValue addAll(Map<Variable, Term> substitution) {
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            if (truthValue == TruthValue.FALSE) {
                break;
            }

            add(entry.getValue(), entry.getKey());
        }

        return truthValue;
    }

    @SuppressWarnings("unchecked")
    private TruthValue addAll(Object... args) {
        for (Object arg : args) {
            if (truthValue == TruthValue.FALSE) {
                break;
            }

            if (arg instanceof SymbolicConstraint) {
                addAll((SymbolicConstraint) arg);
            } else if (arg instanceof Collection) {
                if (((Collection<?>) arg).iterator().hasNext()) {
                    Object element = ((Collection<?>) arg).iterator().next();
                    if (element instanceof Term) {
                        addAll((Collection<Term>) arg);
                    } else {
                        addAll((List<Equality>) arg);
                    }
                }
            } else if (arg instanceof Map) {
                addAll((Map<Variable, Term>) arg);
            } else if (arg instanceof Equality) {
                add((Equality) arg);
            } else {
                assert false : "invalid argument found: " + arg;
            }
        }
        return truthValue;
    }

    public TruthValue addAllThenSimplify(Object... args) {
        addAll(args);
        return simplify();
    }

    public boolean checkUnsat() {
        return context.global().constraintOps.checkUnsat(this);
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
     * Garbage collect useless bindings. This method should be called after
     * applying the substitution to the RHS of a rule. It then removes all
     * bindings of anonymous variables.
     */
    public void eliminateAnonymousVariables(Set<Variable> nonAnonymousVariables) {
        for (Iterator<Variable> iterator = substitution.keySet().iterator(); iterator.hasNext();) {
            Variable variable = iterator.next();
            if (!nonAnonymousVariables.contains(variable)) {
                iterator.remove();
            }
        }

        /* reset this symbolic constraint to be true when it becomes empty */
        if (equalities.isEmpty() && substitution.isEmpty()) {
            truthValue = TruthValue.TRUE;
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

    public boolean implies(SymbolicConstraint constraint, Set<Variable> rightOnlyVariables) {
        // TODO(AndreiS): this can prove "stuff -> false", it needs fixing
        assert !constraint.isFalse();

        LinkedList<Pair<SymbolicConstraint, SymbolicConstraint>> implications = new LinkedList<>();
        implications.add(Pair.of(this, constraint));
        while (!implications.isEmpty()) {
            Pair<SymbolicConstraint, SymbolicConstraint> implication = implications.remove();

            SymbolicConstraint left = implication.getLeft();
            SymbolicConstraint right = implication.getRight();
            if (left.isFalse()) continue;

            if (context.definition().context().globalOptions.debug) {
                System.err.println("Attempting to prove: \n\t" + left + "\n  implies \n\t" + right);
            }

            right.orientSubstitution(rightOnlyVariables);
            right = left.simplifyConstraint(right);
            right.orientSubstitution(rightOnlyVariables);
            if (right.isTrue() || (right.equalities().isEmpty() && rightOnlyVariables.containsAll(right.substitution().keySet()))) {
                if (context.definition().context().globalOptions.debug) {
                    System.err.println("Implication proved by simplification");
                }
                continue;
            }
            IfThenElseFinder ifThenElseFinder = new IfThenElseFinder(context);
            right.accept(ifThenElseFinder);
            if (!ifThenElseFinder.result.isEmpty()) {
                KItem ite = ifThenElseFinder.result.get(0);
                // TODO (AndreiS): handle KList variables
                Term condition = ((KList) ite.kList()).get(0);
                if (context.definition().context().globalOptions.debug) {
                    System.err.println("Split on " + condition);
                }
                SymbolicConstraint left1 = new SymbolicConstraint(left, context);
                left1.add(condition, BoolToken.TRUE);
                implications.add(Pair.of(left1, new SymbolicConstraint(right,context)));
                SymbolicConstraint left2 = new SymbolicConstraint(left, context);
                left2.add(condition, BoolToken.FALSE);
                implications.add(Pair.of(left2, new SymbolicConstraint(right,context)));
                continue;
            }
//            if (DEBUG) {
//                System.out.println("After simplification, verifying whether\n\t" + left.toString() + "\nimplies\n\t" + right.toString());
//            }
            if (!impliesSMT(left,right, rightOnlyVariables)) {
                if (context.definition().context().globalOptions.debug) {
                    System.err.println("Failure!");
                }
                return false;
            } else {
                if (context.definition().context().globalOptions.debug) {
                    System.err.println("Proved!");
                }
            }
        }
       return true;
    }


    private static boolean impliesSMT(
            SymbolicConstraint left,
            SymbolicConstraint right,
            Set<Variable> rightOnlyVariables) {
        assert left.context == right.context;
        return left.context.global().constraintOps.impliesSMT(left, right, rightOnlyVariables);
    }

    /**
     * Simplifies the given constraint by eliding the equalities and substitution entries that are
     * implied by this constraint.
     */
    private SymbolicConstraint simplifyConstraint(SymbolicConstraint constraint) {
        constraint.normalize();

        SymbolicConstraint simplifiedConstraint = new SymbolicConstraint(constraint.termContext());
        MapDifference<Variable, Term> mapDifference = Maps.difference(
                constraint.substitution(),
                substitution());
        simplifiedConstraint.addAll(mapDifference.entriesOnlyOnLeft());
        for (Entry<Variable, ValueDifference<Term>> entry : mapDifference.entriesDiffering().entrySet()) {
            simplifiedConstraint.add(entry.getKey(), entry.getValue().leftValue());
        }
        List<Equality> equalities = new LinkedList<>(constraint.equalities());
        equalities.removeAll(equalities());
        simplifiedConstraint.addAll(equalities);
        simplifiedConstraint.simplify();

        Map<Term, Term> substitution = Maps.newLinkedHashMap();
        for (Equality e1:equalities()) {
            if (e1.rightHandSide().isGround()) {
                substitution.put(e1.leftHandSide(), e1.rightHandSide());
            }
            if (e1.leftHandSide().isGround()) {
                substitution.put(e1.rightHandSide(), e1.leftHandSide());
            }
        }
        simplifiedConstraint = (SymbolicConstraint) substituteTerms(simplifiedConstraint, substitution);
        simplifiedConstraint.renormalize();
        simplifiedConstraint.simplify();
        return simplifiedConstraint;
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
        return equalities.isEmpty() && unifier.data.multiConstraints.isEmpty();
    }

    public boolean isUnknown() {
        normalize();
        return truthValue == TruthValue.UNKNOWN;
    }

    /**
     * Sets this constraint to be false, and record a minimal equality that makes it false.
     * @param equality
     */
    private void falsify(Equality equality) {
        // TODO(AndreiS): this assertion should not fail
        // assert truthValue == TruthValue.TRUE || truthValue == TruthValue.UNKNOWN;
        truthValue = TruthValue.FALSE;
        falsifyingEquality = equality;
    }

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
        return simplify(false);
    }

    public TruthValue simplifyModuloPatternFolding() {
        return simplify(true);
    }

    /**
     * Simplifies this symbolic constraint as much as possible. Decomposes large
     * equalities into small ones using unification.
     *
     * @param fold set if non-deterministic pattern folding is enabled
     *
     * @return the truth value of this symbolic constraint after simplification
     */
    private TruthValue simplify(boolean fold) {
        if (truthValue != TruthValue.UNKNOWN) {
            return truthValue;
        }

        boolean change; // specifies if the equalities have been further
                        // simplified in the last iteration

        label: do {
            change = false;
            normalize();
            if (truthValue != TruthValue.UNKNOWN) {
                return truthValue;
            }

            equalitiesWriteProtected = true;
            for (Iterator<Equality> iterator = equalities.iterator(); iterator.hasNext();) {
                Equality equality = iterator.next();
                if (equality.isSimplifiableByCurrentAlgorithm()) {
                    // if both sides of the equality could be further
                    // decomposed, discharge the equality
                    iterator.remove();
                    if (!unifier.unify(equality)) {
                        falsify(new Equality(
                                unifier.unificationFailureLeftHandSide(), unifier.unificationFailureRightHandSide(), context));
                        equalitiesWriteProtected = false;
                        break label;
                    }

                    change = true;
                } else if (BuiltinMap.isMapUnifiableByCurrentAlgorithm(equality.leftHandSide(), equality.rightHandSide())) {
                    try {
                        if (unifier.simplifyMapEquality(
                                (BuiltinMap) equality.leftHandSide(),
                                (BuiltinMap) equality.rightHandSide(),
                                fold)) {
                            iterator.remove();
                            change = true;
                        }
                    } catch (UnificationFailure e) {
                         falsify(new Equality(
                                unifier.unificationFailureLeftHandSide(), unifier.unificationFailureRightHandSide(), context));
                        equalitiesWriteProtected = false;
                        break label;
                    }
                } else if (equality.leftHandSide() instanceof BuiltinList
                        && ((BuiltinList) equality.leftHandSide()).isUnifiableByCurrentAlgorithm()
                        && equality.rightHandSide() instanceof BuiltinList
                        && ((BuiltinList) equality.rightHandSide()).isUnifiableByCurrentAlgorithm()) {
                    try {
                        if (unifier.unifyList(
                                (BuiltinList) equality.leftHandSide(),
                                (BuiltinList) equality.rightHandSide(), false)) {
                            iterator.remove();
                            change = true;
                        }
                    } catch (UnificationFailure e) {
                         falsify(new Equality(
                                unifier.unificationFailureLeftHandSide(), unifier.unificationFailureRightHandSide(), context));
                        equalitiesWriteProtected = false;
                        break label;
                    }
                }
            }

            equalitiesWriteProtected = false;
        } while (change);

        return truthValue;
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
        assert !equalitiesWriteProtected : "Do not modify equalities when they are write-protected!";

        if (isNormal) {
            return;
        }

        assert !recursiveNormalize : "recursive normalization shall not happen";
        recursiveNormalize = true;
        renormalize();

        /* reset this symbolic constraint to be true when it becomes empty */
        if (equalities.isEmpty() && substitution.isEmpty()) {
            truthValue = TruthValue.TRUE;
        }
        recursiveNormalize = false;
    }

    private void renormalize() {
        isNormal = true;
        equalities.addAll(equalityBuffer);
        equalityBuffer.clear();

        boolean substChanged;
        do {
            substChanged = false;
            Iterator<Equality> iter = equalities.iterator();
            while (iter.hasNext()) {
                Equality equality = iter.next();
                Equality evalEquality = equality.substituteAndEvaluate(substitution);
                boolean equalityChanged = equality != evalEquality;

                if (evalEquality.truthValue() == TruthValue.TRUE) {
                    iter.remove();
                    continue;
                } else if (evalEquality.truthValue() == TruthValue.FALSE) {
                    falsify(evalEquality);
                    return;
                }

                Map<Variable, Term> substToAdd = Maps.newHashMap();
                Term leftHandSide = evalEquality.leftHandSide();
                Term rightHandSide = evalEquality.rightHandSide();
                if (leftHandSide instanceof Variable
                        && rightHandSide instanceof Variable) {
                    if (((Variable) rightHandSide).isAnonymous()) {
                        substToAdd.put((Variable) rightHandSide, leftHandSide);
                    } else {
                        substToAdd.put((Variable) leftHandSide, rightHandSide);
                    }
                    /* TODO(YilongL): investigate why the following code will break the prover */
//                    if (leftHandSide.sort().equals(rightHandSide.sort())) {
//                        if (((Variable) rightHandSide).isAnonymous()) {
//                            substToAdd.put((Variable) rightHandSide, leftHandSide);
//                        } else {
//                            substToAdd.put((Variable) leftHandSide, rightHandSide);
//                        }
//                    } else {
//                        Sort glb = context.definition().subsorts().getGLBSort(leftHandSide.sort(), rightHandSide.sort());
//                        if (glb != null) {
//                            Variable variable = Variable.getFreshVariable(glb);
//                            substToAdd.put((Variable) leftHandSide, variable);
//                            substToAdd.put((Variable) rightHandSide, variable);
//                        } else {
//                            if (equalityChanged) {
//                                iter.remove();
//                                equalityBuffer.add(evalEquality);
//                            }
//                            continue;
//                        }
//                    }
                } else if (leftHandSide instanceof Variable) {
                    substToAdd.put((Variable) leftHandSide, rightHandSide);
                } else if (rightHandSide instanceof Variable) {
                    substToAdd.put((Variable) rightHandSide, leftHandSide);
                } else {
                    if (equalityChanged) {
                        iter.remove();
                        equalityBuffer.add(evalEquality);
                    }
                    continue;
                }

                boolean occursCheck = false;
                for (Variable key : substToAdd.keySet()) {
                    occursCheck = occursCheck || substToAdd.get(key).variableSet().contains(key);
                }

                if (!occursCheck) {
                    iter.remove();
                    // TODO(YilongL): composeSubstitution seems ad-hoc... FIXME!
                    composeSubstitution(substToAdd, context);
                    if (truthValue == TruthValue.FALSE) {
                        return;
                    }

                    substChanged = true;
                    break;
                } else {
                    if (equalityChanged) {
                        iter.remove();
                        equalityBuffer.add(evalEquality);
                    }
                }
            }

            equalities.addAll(equalityBuffer);
            equalityBuffer.clear();
        } while (substChanged);
    }

    public void expandPatternsAndSimplify(boolean narrowing) {
        normalize();

        boolean changed;
        do {
            changed = false;
            // TODO(AndreiS): patterns should be expanded before are put in the substitution
            Set<Variable> keys = Sets.newLinkedHashSet(substitution.keySet());
            for (Variable variable : keys) {
                Term term = substitution.get(variable);
                Term expandedTerm = term.expandPatterns(this, narrowing, context);
                if (term != expandedTerm) {
                    substitution.put(variable, expandedTerm);
                    changed = true;
                }
            }

            // TODO(YilongL): what if this SymbolicConstraint is modified inside the loop?
            // TODO(YilongL): this is too ad-hoc; fix it once we allow sub-terms to carry constraint as well
            int origSize = equalities.size();
            for (int i = 0; i < equalities.size(); ++i) {
                Equality equality = equalities.remove(i);
                Equality expandedEquality = equality.expandPatterns(this, narrowing);
                equalities.addFirst(expandedEquality);
                if (equality != expandedEquality) {
                    changed = true;
                    if (equalities.size() != origSize) {
                        break;
                    }
                }
            }

            /* force normalization to consider the changes made by this method */
            isNormal = false;

            // TODO(AndreiS): move folding from here (this is way too fragile)
            /* simplify with pattern folding if not performing narrowing */
            if (!narrowing) {
                simplify(true);
            } else {
                simplify();
            }
        } while (changed);
    }

    /**
     * Private helper method that composes a specified substitution map with the
     * substitution map of this symbolic constraint.
     *
     * @param substMap
     *            the specified substitution map
     * @param context
     *            the term context
     */
    private void composeSubstitution(Map<Variable, Term> substMap,
            TermContext context) {
        @SuppressWarnings("unchecked")
        Map.Entry<Variable, Term>[] entries = substitution.entrySet().toArray(new Map.Entry[substitution.size()]);
        for (Map.Entry<Variable, Term> subst : entries) {
            Term term = subst.getValue().substituteAndEvaluate(substMap, context);
            if (term != subst.getValue()) {
                checkTruthValBeforePutIntoConstraint(subst.getKey(), term, true);
            }
        }

        // on composing two substitution maps:
        // http://www.mathcs.duq.edu/simon/Fall04/notes-7-4/node4.html
        Set<Variable> variables = Sets.newLinkedHashSet(substitution.keySet());
        variables.retainAll(substMap.keySet());
        assert variables.isEmpty() :
            "There shall be no common variables in the two substitution maps to be composed.";
        substitution.putAll(substMap);
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
            entry.setValue(entry.getValue().substituteWithBinders(freshSubstitution, context));
        }

        for (int i = 0; i < equalities.size(); ++i) {
            equalities.set(i, equalities.get(i).substitute(freshSubstitution));
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
     * Checks if this symbolic constraint is a matching substitution of the variables in the
     * argument set.
     */
    public boolean isMatching(Set<Variable> variables) {
        orientSubstitution(variables);
        /*
         * YilongL: data structure lookups will change the variables on the LHS
         * of a rule, e.g.: "rule foo(M:Map X |-> Y, X) => 0" will be kompiled
         * into "rule foo(_,_)(_0:Map,, X) => 0 requires [] /\ _0:Map[X] = Y
         * ensures []". Therefore, we cannot write pattern.term().variableSet()
         * in the following check.
         */
        if (!isSubstitution() || !substitution.keySet().equals(variables)) {
            return false;
        }

        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
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
            if (!context.definition().subsorts().isSubsortedEq(sortOfPatVar, sortOfSubst)) {
                return false;
            }

            if (entry.getKey() instanceof ConcreteCollectionVariable
                    && !(entry.getValue() instanceof ConcreteCollectionVariable && ((ConcreteCollectionVariable) entry.getKey()).concreteCollectionSize() == ((ConcreteCollectionVariable) entry.getValue()).concreteCollectionSize())
                    && !(entry.getValue() instanceof org.kframework.backend.java.kil.Collection && !((org.kframework.backend.java.kil.Collection) entry.getValue()).hasFrame() && ((ConcreteCollectionVariable) entry.getKey()).concreteCollectionSize() == ((org.kframework.backend.java.kil.Collection) entry.getValue()).concreteSize())) {
                return false;
            }
        }
        return true;
    }

    public boolean hasMapEqualities() {
        for (Equality equality : equalities) {
            if (equality.leftHandSide() instanceof BuiltinMap
                    && equality.rightHandSide() instanceof BuiltinMap) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean equals(Object object) {
        // TODO(AndreiS): canonicalize
        if (this == object) {
            return true;
        }

        if (!(object instanceof SymbolicConstraint)) {
            return false;
        }

        SymbolicConstraint constraint = (SymbolicConstraint) object;
        return substitution.equals(constraint.substitution)
                && equalities.equals(constraint.equalities);
    }

    @Override
    public int hashCode() {
        // TODO(YilongL): canonicalize
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + substitution.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + equalities.hashCode();
        return hashCode;
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

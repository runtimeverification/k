// Copyright (c) 2013-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import static org.kframework.backend.java.util.RewriteEngineUtils.isSubsorted;
import static org.kframework.backend.java.util.RewriteEngineUtils.isSubsortedEq;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.AndOrTree;
import org.kframework.backend.java.util.AndOrTree.NodeType;
import org.kframework.backend.java.util.RewriteEngineUtils;
import org.kframework.backend.java.util.Utils;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.kil.ASTNode;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.SMTSolver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;
import com.google.common.collect.MapDifference;
import com.google.common.collect.MapDifference.ValueDifference;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.inject.Inject;
import com.google.inject.Provider;

/**
 * A conjunction of equalities between terms (with variables).
 *
 * @author AndreiS
 */
public class SymbolicConstraint extends JavaSymbolicObject {

    public static final String SEPARATOR = " /\\ ";

    private static final Joiner JOINER = Joiner.on(SEPARATOR);

    private static final Joiner.MapJoiner SUBSTITUTION_JOINER
            = JOINER.withKeyValueSeparator(Equality.SEPARATOR);

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
    private LinkedHashSet<Equality> equalities;

    /**
     * Specifies if this symbolic constraint is in normal form.
     * <p>
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
     * Invariants:
     * <li> {@code Variable}s on the left-hand sides do not occur in the
     * {@code Term}s on the right-hand sides;
     * <li>the invariant of {@code SymbolicConstraint#equalities} also applies
     * here.
     *
     * @see SymbolicConstraint#equalities
     */
    private LinkedHashMap<Variable, Term> substitution;

    private TruthValue truthValue;

    /**
     * Stores the minimal equality causing this constraint to become false.
     * It is null is this constraint is not false.
     */
    private Equality falsifyingEquality;

    private final LinkedHashSet<Equality> equalityBuffer = Sets.newLinkedHashSet();

    private boolean writeProtected = false;

    private List<AndOrTree<SymbolicConstraint>> multiConstraints = Lists.newArrayList();

    private final TermContext context;

    @Deprecated
    public boolean orientSubstitution(Set<Variable> variables) {
        LinkedHashMap<Variable, Term> substitutionBackup = Maps.newLinkedHashMap(substitution);

        Map<Variable, Term> newSubstitution = Maps.newLinkedHashMap();
        if (substitution.keySet().containsAll(variables)) {
            /* avoid setting isNormal to false */
            return true;
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
                        substitution = substitutionBackup;
                        return false;
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

        LinkedHashMap<Variable, Term> result = Maps.newLinkedHashMap();
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

        if (!result.keySet().containsAll(variables)) {
            substitution = substitutionBackup;
            return false;
        }
        for (Map.Entry<Variable, Term> subst : result.entrySet()) {
            Equality equality = new Equality(subst.getKey(), subst.getValue(), context);
            if (!isSubsortedEq(subst.getKey(), subst.getValue(), context)
                    || equality.truthValue() == TruthValue.FALSE) {
                substitution = substitutionBackup;
                return false;
            }
        }
        substitution = result;

        /*
         * after re-orientation, the {@code equalities} may contain variables on
         * the LHS's of the {@code substitution}
         */
        isNormal = false;
        return true;
    }

    public static class SymbolicConstraintOperations {

        private final SMTOptions smtOptions;
        private final Z3Wrapper z3;

        @Inject
        public SymbolicConstraintOperations(
                Provider<Definition> definitionProvider,
                SMTOptions smtOptions,
                Z3Wrapper z3) {
            this.smtOptions = smtOptions;
            this.z3 = z3;
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
                String query = KILtoSMTLib.translateConstraint(constraint);
                result = z3.checkQuery(query, smtOptions.z3CnstrTimeout);
                if (result && RuleAuditing.isAuditBegun()) {
                    System.err.println("SMT query returned unsat: " + query);
                }
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
        constraint.addAllThenSimplify(args);
        return constraint;
    }

    public SymbolicConstraint(SymbolicConstraint constraint) {
        this(constraint.context);
        assert constraint.isNormal : "the given constraint is not normalized";
        substitution = Maps.newLinkedHashMap(constraint.substitution);
        equalities = Sets.newLinkedHashSet(constraint.equalities);
        truthValue = constraint.truthValue;
        isNormal = constraint.isNormal;
    }

    public SymbolicConstraint(TermContext context) {
        substitution = Maps.newLinkedHashMap();
        equalities = Sets.newLinkedHashSet();
        truthValue = TruthValue.TRUE;
        isNormal = true;
        this.context = context;
    }

    /**
     * @return an unmodifiable view of the field {@code equalities}
     */
    public Set<Equality> equalities() {
        normalize();
        return Collections.unmodifiableSet(equalities);
    }

    /**
     * @return an unmodifiable view of the field {@code substitution}
     */
    public Map<Variable, Term> substitution() {
        normalize();
        return Collections.unmodifiableMap(substitution);
    }

    public Equality falsifyingEquality() {
        return falsifyingEquality;
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
     */
    public void add(Term leftHandSide, Term rightHandSide) {
        /* split andBool in multiple equalities */
        // TODO(YilongL): maybe this should be handled somewhere else?
        if (leftHandSide instanceof KItem && ((KItem) leftHandSide).kLabel().toString().equals("'_andBool_") && rightHandSide.equals(BoolToken.TRUE)) {
            add(((KList) ((KItem) leftHandSide).kList()).get(0), BoolToken.TRUE);
            add(((KList) ((KItem) leftHandSide).kList()).get(1), BoolToken.TRUE);
            return;
        }

        /* split andBool in multiple equalities */
        if (rightHandSide instanceof KItem && ((KItem) rightHandSide).kLabel().toString().equals("'_andBool_") && leftHandSide.equals(BoolToken.TRUE)) {
            add(((KList) ((KItem) rightHandSide).kList()).get(0), BoolToken.TRUE);
            add(((KList) ((KItem) rightHandSide).kList()).get(1), BoolToken.TRUE);
            return;
        }

        /* simplify orBool in multiple equalities */
        if (leftHandSide instanceof KItem && ((KItem) leftHandSide).kLabel().toString().equals("'_orBool_") && rightHandSide.equals(BoolToken.FALSE)) {
            add(((KList) ((KItem) leftHandSide).kList()).get(0), BoolToken.FALSE);
            add(((KList) ((KItem) leftHandSide).kList()).get(1), BoolToken.FALSE);
            return;
        }

        /* simplify orBool in multiple equalities */
        if (rightHandSide instanceof KItem && ((KItem) rightHandSide).kLabel().toString().equals("'_orBool_") && leftHandSide.equals(BoolToken.FALSE)) {
            add(((KList) ((KItem) rightHandSide).kList()).get(0), BoolToken.FALSE);
            add(((KList) ((KItem) rightHandSide).kList()).get(1), BoolToken.FALSE);
            return;
        }

        /* simplify notBool */
        if (leftHandSide instanceof KItem && ((KItem) leftHandSide).kLabel().toString().equals("'notBool_") && rightHandSide instanceof BoolToken) {
            add(((KList) ((KItem) leftHandSide).kList()).get(0), BoolToken.of(!((BoolToken) rightHandSide).booleanValue()));
            return;
        }
        if (rightHandSide instanceof KItem && ((KItem) rightHandSide).kLabel().toString().equals("'notBool_") && leftHandSide instanceof BoolToken) {
            add(((KList) ((KItem) rightHandSide).kList()).get(0), BoolToken.of(!((BoolToken) leftHandSide).booleanValue()));
            return;
        }

        Equality equality = new Equality(leftHandSide, rightHandSide, context);
        if (writeProtected) {
            if (equalityBuffer.add(equality)) {
                isNormal = false;
                truthValue = TruthValue.UNKNOWN;
            }
        } else {
            if (equalities.add(equality)) {
                isNormal = false;
                truthValue = TruthValue.UNKNOWN;
            }
        }
    }

    /**
     * Adds a given equality to this symbolic constraint.
     */
    public void add(Equality equality) {
        add(equality.leftHandSide(), equality.rightHandSide());
    }

    /**
     * Adds the side condition of a rule to this symbolic constraint. The side
     * condition is represented as a list of {@code Term}s that are expected to
     * be equal to {@code BoolToken#TRUE}.
     */
    public void addAll(List<Term> condition) {
        for (Term term : condition) {
            add(term, BoolToken.TRUE);
        }
    }

    private void addAll(Set<Equality> equalites) {
        for (Equality equality : equalites) {
            add(equality);
        }
    }

    /**
     * Adds all equalities in the given symbolic constraint to this one.
     *
     * @param constraint
     *            the given symbolic constraint
     */
    public void addAll(SymbolicConstraint constraint) {
        addAll(constraint.substitution);
        addAll(constraint.equalities);
    }

    /**
     * Adds all bindings in the given substitution map to this symbolic constraint.
     */
    public void addAll(Map<Variable, Term> substitution) {
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            add(entry.getValue(), entry.getKey());
        }
    }

    @SuppressWarnings("unchecked")
    private void addAll(Object... args) {
        for (Object arg : args) {
            if (arg instanceof SymbolicConstraint) {
                addAll((SymbolicConstraint) arg);
            } else if (arg instanceof Collection) {
                if (((Collection<?>) arg).iterator().hasNext()) {
                    Object element = ((Collection<?>) arg).iterator().next();
                    if (element instanceof Term) {
                        addAll((List<Term>) arg);
                    } else {
                        addAll((Set<Equality>) arg);
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
    }

    public TruthValue addAllThenSimplify(Object... args) {
        addAll(args);
        return simplify();
    }

    public boolean checkUnsat() {
        return context.global().constraintOps.checkUnsat(this);
    }

    /**
     * Removes specified variable bindings from this constraint.
     * <p>
     * Note: this method should only be used to garbage collect useless
     * bindings. It is called to remove all bindings of the rewrite rule
     * variables after building the rewrite result.
     */
    public void removeBindings(Set<Variable> variablesToRemove) {
        substitution.keySet().removeAll(variablesToRemove);

        /* reset this symbolic constraint to be true when it becomes empty */
        if (equalities.isEmpty() && substitution.isEmpty() && multiConstraints.isEmpty()) {
            truthValue = TruthValue.TRUE;
        }
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
                SymbolicConstraint left1 = new SymbolicConstraint(left);
                left1.add(condition, BoolToken.TRUE);
                implications.add(Pair.of(left1, new SymbolicConstraint(right)));
                SymbolicConstraint left2 = new SymbolicConstraint(left);
                left2.add(condition, BoolToken.FALSE);
                implications.add(Pair.of(left2, new SymbolicConstraint(right)));
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
        Predicate<Equality> inConstraint = equality -> !equalities().contains(equality)
                && !equalities().contains(new Equality(equality.rightHandSide(), equality.leftHandSide(), context));
        Set<Equality> equalities = constraint.equalities().stream()
                .filter(inConstraint)
                .collect(Collectors.toSet());
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
        simplifiedConstraint = (SymbolicConstraint) TermSubstitutionTransformer
                .substitute(simplifiedConstraint, substitution, context);
        simplifiedConstraint.renormalize();
        simplifiedConstraint.simplify();
        return simplifiedConstraint;
    }

    public boolean isFalse() {
        if (truthValue == TruthValue.FALSE) {
            return true;
        } else {
            normalize();
            return truthValue == TruthValue.FALSE;
        }
    }

    public boolean isTrue() {
        normalize();
        return truthValue == TruthValue.TRUE;
    }

    public boolean isSubstitution() {
        normalize();
        return equalities.isEmpty() && multiConstraints.isEmpty();
    }

    /**
     * Sets this constraint to be false, and record a minimal equality that makes it false.
     * @param equality
     */
    private void falsify(Equality equality) {
        // TODO(AndreiS): this assertion should not fail
        assert truthValue == TruthValue.TRUE || truthValue == TruthValue.UNKNOWN;
        if (RuleAuditing.isAuditBegun()) {
            System.err.println("Unification failure: " + equality.leftHandSide()
            + " does not unify with " + equality.rightHandSide());
        }
        truthValue = TruthValue.FALSE;
        isNormal = true;
        falsifyingEquality = equality;
    }

    public List<SymbolicConstraint> getMultiConstraints() {
        return RewriteEngineUtils.getMultiConstraints(this, multiConstraints);
    }

    /**
     * Simplifies this symbolic constraint as much as possible. Decomposes large
     * equalities into small ones using unification.
     *
     * @return the truth value of this symbolic constraint after simplification
     */
    public TruthValue simplify() {
        return simplify(false, true);
    }

    /**
     * Similar to {@link SymbolicConstraint#simplify()} except that equalities
     * between builtin data structures will remain intact if they cannot be
     * resolved completely.
     */
    public TruthValue simplifyBeforePatternFolding() {
        return simplify(false, false);
    }

    public TruthValue simplifyModuloPatternFolding() {
        return simplify(true, true);
    }

    /**
     * Simplifies this symbolic constraint as much as possible. Decomposes large
     * equalities into small ones using unification.
     *
     * @param patternFold
     *            set if non-deterministic pattern folding is enabled
     *
     * @param partialSimpl
     *            set if equalities between builtin data structures can be
     *            partially simplified
     *
     * @return the truth value of this symbolic constraint after simplification
     */
    private TruthValue simplify(boolean patternFold, boolean partialSimpl) {
        if (truthValue != TruthValue.UNKNOWN) {
            return truthValue;
        }

        Map<Variable, Term> oldSubst = null;
        Set<Equality> oldEqualities = null;

        while (true) {
            normalize();
            if (truthValue != TruthValue.UNKNOWN) {
                return truthValue;
            }

            if (oldSubst != null && oldEqualities != null
                    && substitution.equals(oldSubst)
                    && equalities.equals(oldEqualities)) {
                break;
            }
            oldSubst = Maps.newHashMap(substitution);
            oldEqualities = Sets.newHashSet(equalities);

            writeProtected = true;
            for (Iterator<Equality> iterator = equalities.iterator(); iterator.hasNext();) {
                Equality equality = iterator.next();

                SymbolicUnifier unifier = new SymbolicUnifier(patternFold, partialSimpl, context);
                if (!unifier.symbolicUnify(equality.leftHandSide(), equality.rightHandSide())) {
                    falsify(new Equality(
                            unifier.unificationFailureLeftHandSide(),
                            unifier.unificationFailureRightHandSide(), context));
                    return TruthValue.FALSE;
                }

                if (equality.leftHandSide() instanceof Variable && equality.rightHandSide().isNormal()
                        && equality.rightHandSide().variableSet().contains(equality.leftHandSide())) {
                    falsify(equality);
                    return TruthValue.FALSE;
                } else if (equality.rightHandSide() instanceof Variable && equality.leftHandSide().isNormal()
                        && equality.leftHandSide().variableSet().contains(equality.rightHandSide())) {
                    falsify(equality);
                    return TruthValue.FALSE;
                }

                if (unifier.multiConstraints().getNodeType() == NodeType.LEAF
                        && unifier.constraint().equalities.size() == 1
                        && unifier.constraint().equalities.iterator().next().equals(equality)) {
                    continue;
                }

                iterator.remove();
                if (unifier.multiConstraints().getNodeType() == NodeType.LEAF) {
                    addAll(unifier.multiConstraints().getLeaf());
                } else {
                    multiConstraints.add(unifier.multiConstraints());
                }
            }

            writeProtected = false;
        }

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
        if (truthValue == TruthValue.FALSE) {
            return;
        }

//        assert !equalitiesWriteProtected : "Do not modify equalities when they are write-protected!";
        if (isNormal || writeProtected) {
            return;
        }

        assert !recursiveNormalize : "recursive normalization shall not happen";
        recursiveNormalize = true;
        renormalize();

        /* reset this symbolic constraint to be true when it becomes empty */
        if (equalities.isEmpty() && substitution.isEmpty() && multiConstraints.isEmpty()) {
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
                    falsify(equality.substitute(substitution));
                    return;
                }

                Map<Variable, Term> substToAdd = Maps.newLinkedHashMap();
                Term lhs = evalEquality.leftHandSide();
                Term rhs = evalEquality.rightHandSide();
                if (lhs instanceof Variable
                        && rhs instanceof Variable) {
                    if (isSubsorted(lhs, rhs, context)) {
                        substToAdd.put((Variable) lhs, rhs);
                    } else if (isSubsorted(rhs, lhs, context)) {
                        substToAdd.put((Variable) rhs, lhs);
                    } else if (lhs.sort().equals(rhs.sort())) {
                        if (((Variable) rhs).isAnonymous()) {
                            substToAdd.put((Variable) rhs, lhs);
                        } else {
                            substToAdd.put((Variable) lhs, rhs);
                        }
                    } else {
                        if (equalityChanged) {
                            iter.remove();
                            equalityBuffer.add(evalEquality);
                        }
                        continue;
                    }
                } else if (lhs instanceof Variable && isSubsortedEq(lhs, rhs, context)) {
                    substToAdd.put((Variable) lhs, rhs);
                } else if (rhs instanceof Variable && isSubsortedEq(rhs, lhs, context)) {
                    substToAdd.put((Variable) rhs, lhs);
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
                    composeSubstitution(substToAdd);
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
        Map<Variable, Term> oldSubst = null;
        Set<Equality> oldEqualities = null;

        normalize();
        while (truthValue == TruthValue.UNKNOWN) {
            assert isNormal;
            if (oldSubst != null && oldEqualities != null
                    && substitution.equals(oldSubst)
                    && equalities.equals(oldEqualities)) {
                break;
            }
            oldSubst = Maps.newHashMap(substitution);
            oldEqualities = Sets.newHashSet(equalities);

            // TODO(AndreiS): patterns should be expanded before are put in the substitution
            Set<Variable> keys = Sets.newLinkedHashSet(substitution.keySet());
            writeProtected = true;
            for (Variable variable : keys) {
                Term term = substitution.get(variable);
                Term expandedTerm = term.expandPatterns(this, narrowing);
                if (term != expandedTerm) {
                    substitution.put(variable, expandedTerm);
                }
            }

            LinkedHashSet<Equality> expandedEqualities = Sets.newLinkedHashSet();
            for (Equality equality : equalities) {
                Equality expandedEquality = equality.expandPatterns(this, narrowing);
                expandedEqualities.add(expandedEquality);
            }
            equalities = expandedEqualities;
            writeProtected = false;

            /* force normalization to consider the changes made by this method */
            isNormal = false;

            // TODO(AndreiS): move folding from here (this is way too fragile)
            /* simplify with pattern folding if not performing narrowing */
            if (!narrowing) {
                simplifyModuloPatternFolding();
            } else {
                simplify();
            }
        }
    }

    /**
     * Private helper method that composes a specified substitution map with the
     * substitution map of this symbolic constraint.
     *
     * @param substMap
     *            the specified substitution map
     */
    private void composeSubstitution(Map<Variable, Term> substMap) {
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            Term variable = entry.getKey();
            Term term = entry.getValue().substituteAndEvaluate(substMap, context);
            Equality equality = new Equality(variable, term, context);
            if (equality.truthValue() == TruthValue.UNKNOWN) {
                entry.setValue(term);
            } else if (equality.truthValue() == TruthValue.FALSE) {
                falsify(equality);
                return;
            }
        }

        // on composing two substitution maps:
        // http://www.mathcs.duq.edu/simon/Fall04/notes-7-4/node4.html
        assert Sets.intersection(substitution.keySet(), substMap.keySet()).isEmpty() :
            "There shall be no common variables in the two substitution maps to be composed.";
        substitution.putAll(substMap);
    }

    /**
     * Checks if this symbolic constraint contains only substitutions of the
     * given variables.
     * <p>
     * This method is useful for checking if narrowing happens.
     */
    public boolean isMatching(Set<Variable> variables) {
        if (!isSubstitution()) {
            return false;
        }

        return orientSubstitution(variables)
                && substitution.size() == variables.size();
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
    public Set<Variable> variableSet() {
        // TODO(YilongL): get rid of this once SymbolicConstraint becomes immutable
        setVariableSet(null);
        return super.variableSet();
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
        builder = JOINER.appendTo(builder, equalities);
        if (!(builder.length() == 0) && !substitution.isEmpty()) {
            builder.append(SEPARATOR);
        }
        builder = SUBSTITUTION_JOINER.appendTo(builder, substitution);
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

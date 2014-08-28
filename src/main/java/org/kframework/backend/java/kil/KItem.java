// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.SymbolicRewriter;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import com.google.inject.Inject;


/**
 * Represents a K application which applies a {@link KLabel} to a {@link KList}.
 * Or in the usual syntax of K, it can be defined as the following:
 * <p>
 * <blockquote>
 *
 * <pre>
 * syntax KItem ::= KLabel "(" KList ")"
 * </pre>
 *
 * </blockquote>
 * <p>
 *
 * @author AndreiS
 */
@SuppressWarnings("serial")
public final class KItem extends Term {

    private static final Table<Definition, CacheTableColKey, CacheTableValue> SORT_CACHE_TABLE = HashBasedTable.create();

    private final Term kLabel;
    private final Term kList;
    private final boolean isExactSort;
    private final Sort sort;
    private Boolean evaluable = null;
    private Boolean anywhereApplicable = null;

    public static KItem of(Term kLabel, Term kList, TermContext termContext) {
        /* YilongL: since KList.Builder always canonicalizes its result, the
         * following conversion is necessary */
        kList = KCollection.upKind(kList, Kind.KLIST);

        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            if (kLabelConstant.isListLabel()) {
                return kLabelConstant.getListTerminator();
            }
        }

        return new KItem(kLabel, kList, termContext);
    }

    KItem(Term kLabel, Term kList, Sort sort, boolean isExactSort) {
        super(Kind.KITEM);
        this.kLabel = kLabel;
        this.kList = kList;
        this.sort = sort;
        this.isExactSort = isExactSort;
    }

    private KItem(Term kLabel, Term kList, TermContext termContext) {
        super(Kind.KITEM);
        this.kLabel = kLabel;
        this.kList = kList;

        Definition definition = termContext.definition();

        if (kLabel instanceof KLabelConstant && kList instanceof KList
                && !((KList) kList).hasFrame()) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

            /* at runtime, checks if the result has been cached */
            CacheTableColKey cacheTabColKey = null;
            CacheTableValue cacheTabVal = null;
            boolean enableCache = (Tool.instance() != Tool.KOMPILE)
                    && definition.sortPredicateRulesOn(kLabelConstant).isEmpty();
            if (enableCache) {
                cacheTabColKey = new CacheTableColKey(kLabelConstant, (KList) kList);
                cacheTabVal = SORT_CACHE_TABLE.get(definition, cacheTabColKey);
                if (cacheTabVal != null) {
                    sort = cacheTabVal.sort;
                    isExactSort = cacheTabVal.isExactSort;
                    return;
                }
            }

            /* cache miss, compute sort information and cache it */
            cacheTabVal = computeSort(kLabelConstant, (KList) kList, termContext);
            if (enableCache) {
                SORT_CACHE_TABLE.put(definition, cacheTabColKey, cacheTabVal);
            }

            sort = cacheTabVal.sort;
            isExactSort = cacheTabVal.isExactSort;
        } else {
            /* not a KLabelConstant or the kList contains a frame variable */
            if (kLabel instanceof KLabelInjection) {
                assert kList.equals(KList.EMPTY);
            }

            sort = kind.asSort();
            isExactSort = false;
        }
    }

    private CacheTableValue computeSort(KLabelConstant kLabelConstant,
            KList kList, TermContext termContext) {
        Definition definition = termContext.definition();
        Subsorts subsorts = definition.subsorts();

        Set<Sort> sorts = Sets.newHashSet();
        Set<Sort> possibleSorts = Sets.newHashSet();

        if (Tool.instance() != Tool.KOMPILE) {
            /**
             * Sort checks in the Java engine are not implemented as
             * rewrite rules, so we need to precompute the sort of
             * terms. However, right now, we also want to allow users
             * to provide user-defined sort predicate rules, e.g.
             *      ``rule isVal(cons V:Val) => true''
             * to express the same meaning as overloaded productions
             * which are not allowed to write in the current front-end.
             */
            /* YilongL: user-defined sort predicate rules are interpreted as overloaded productions at runtime */
            for (Rule rule : definition.sortPredicateRulesOn(kLabelConstant)) {
                if (MetaK.matchable(kList, rule.sortPredicateArgument().kList(), termContext)
                        .equals(BoolToken.TRUE)) {
                    sorts.add(rule.predicateSort());
                } else if (MetaK.unifiable(kList, rule.sortPredicateArgument().kList(), termContext)
                        .equals(BoolToken.TRUE)) {
                    possibleSorts.add(rule.predicateSort());
                }
            }
        }

        for (Production production : kLabelConstant.productions()) {
            boolean mustMatch = true;
            boolean mayMatch = true;

            if (kList.concreteSize() == production.getArity()) {
                /* check if the production can match this KItem */
                int idx = 0;
                for (Term term : kList) {
                    if (!mayMatch) {
                        break;
                    }

                    Sort childSort = term.sort();
                    if (!definition.context().isSubsortedEq(production.getChildSort(idx), childSort.toFrontEnd())) {
                        mustMatch = false;
                        /*
                         * YilongL: the following analysis can be made more
                         * precise by considering all possible sorts of the
                         * term; however, it would be too expensive to
                         * compute for our purpose
                         */
                        mayMatch = !term.isExactSort()
                                && definition.context().hasCommonSubsort(production.getChildSort(idx), childSort.toFrontEnd());
                    }
                    idx++;
                }
            } else {
                mustMatch = mayMatch = false;
            }

            if (mustMatch) {
                sorts.add(Sort.of(production.getSort()));
            } else if (mayMatch) {
                possibleSorts.add(Sort.of(production.getSort()));
            }
        }

        /*
         * YilongL: we are taking the GLB of all sorts because it is the
         * most precise sort information we can get without losing
         * information. e.g. sorts = [Types, #ListOfId{","}, Exps] => sort =
         * #ListOfId{","}. On the other hand, if the GLB doesn't exist, then
         * we must have an ambiguous grammar with which this KItem cannot be
         * correctly parsed.
         */
        Sort sort = sorts.isEmpty() ? kind.asSort() : subsorts.getGLBSort(sorts);
        if (sort == null) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.CRITICAL, "Cannot compute least sort of term: " +
                            this.toString() + "\nPossible least sorts are: " + sorts));
        }
        /* the sort is exact iff the klabel is a constructor and there is no other possible sort */
        boolean isExactSort = kLabelConstant.isConstructor() && possibleSorts.isEmpty();

        return new CacheTableValue(sort, isExactSort);
    }

    public boolean isEvaluable(TermContext context) {
        if (evaluable != null) {
            return evaluable;
        }

        evaluable = false;
        if (!(kLabel instanceof KLabelConstant)) {
            return false;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

        if (!(kList instanceof KList)) {
            return false;
        }

        if (kLabelConstant.isSortPredicate()
                || !context.definition().functionRules().get(kLabelConstant).isEmpty()
                || context.global().builtins.isBuiltinKLabel(kLabelConstant)) {
            evaluable = true;
        }
        return evaluable;
    }

    public Term evaluateFunction(boolean copyOnShareSubstAndEval, TermContext context) {
        return context.global().kItemOps.evaluateFunction(this, copyOnShareSubstAndEval, context);
    }

    public Term resolveFunctionAndAnywhere(boolean copyOnShareSubstAndEval, TermContext context) {
        return context.global().kItemOps.resolveFunctionAndAnywhere(this, copyOnShareSubstAndEval, context);
    }

    public static class KItemOperations {

        private final Tool tool;
        private final JavaExecutionOptions javaOptions;
        private final GlobalOptions globalOptions;

        @Inject
        public KItemOperations(
                Tool tool,
                JavaExecutionOptions javaOptions,
                GlobalOptions globalOptions) {
            this.tool = tool;
            this.javaOptions = javaOptions;
            this.globalOptions = globalOptions;
        }

        /**
         * Evaluates this {@code KItem} if it is a predicate or function; otherwise,
         * applies [anywhere] rules associated with this {@code KItem}
         *
         * @param copyOnShareSubstAndEval
         *            specifies whether to use
         *            {@link CopyOnShareSubstAndEvalTransformer} when applying rules
         *
         * @param context
         *            a term context
         *
         * @return the reduced result on success, or this {@code KItem} otherwise
         */
        public Term resolveFunctionAndAnywhere(KItem kItem, boolean copyOnShareSubstAndEval, TermContext context) {
            return kItem.isEvaluable(context) ?
                    evaluateFunction(kItem, copyOnShareSubstAndEval, context) :
                    kItem.applyAnywhereRules(copyOnShareSubstAndEval, context);
        }

        /**
         * Evaluates this {@code KItem} if it is a predicate or function
         *
         * @param copyOnShareSubstAndEval
         *            specifies whether to use
         *            {@link CopyOnShareSubstAndEvalTransformer} when applying
         *            user-defined function rules
         *
         * @param context
         *            a term context
         *
         * @return the evaluated result on success, or this {@code KItem} otherwise
         */
        public Term evaluateFunction(KItem kItem, boolean copyOnShareSubstAndEval, TermContext context) {
            if (!kItem.isEvaluable(context)) {
                return kItem;
            }

            Definition definition = context.definition();
            KLabelConstant kLabelConstant = (KLabelConstant) kItem.kLabel;

            KList kList = (KList) kItem.kList;

            if (context.global().builtins.isBuiltinKLabel(kLabelConstant)) {
                try {
                    Term[] arguments = kList.getContents().toArray(new Term[kList.getContents().size()]);
                    Term result = context.global().builtins.invoke(context, kLabelConstant, arguments);
                    if (result != null) {
                        assert result.kind() == Kind.KITEM:
                            "unexpected kind " + result.kind() + " of term " + result + ";"
                            + "expected kind " + Kind.KITEM + " instead";
                        return result;
                    }
                } catch (IllegalAccessException | IllegalArgumentException e) {
                } catch (InvocationTargetException e) {
                    Throwable t = e.getTargetException();
                    if (t instanceof Error) {
                        throw (Error)t;
                    }
                    if (t instanceof KExceptionManager.KEMException) {
                        throw (RuntimeException)t;
                    }
                    if (t instanceof RuntimeException) {
                        if (globalOptions.verbose) {
                            System.err.println("Ignored exception thrown by hook " + kLabelConstant + " : ");
                            e.printStackTrace();
                        }
                    } else {
                        throw new AssertionError("Builtin functions should not throw checked exceptions", e);
                    }
                }
            }

            /* evaluate a sort membership predicate */
            // TODO(YilongL): maybe we can move sort membership evaluation after
            // applying user-defined rules to allow the users to provide their
            // own rules for checking sort membership
            if (kLabelConstant.isSortPredicate() && kList.getContents().size() == 1) {
                Term checkResult = SortMembership.check(kItem, context.definition());
                if (checkResult != kItem) {
                    return checkResult;
                }
            }

            /* apply rules for user defined functions */
            if (!definition.functionRules().get(kLabelConstant).isEmpty()) {
                Term result = null;

                LinkedHashSet<Term> owiseResults = new LinkedHashSet<Term>();
                for (Rule rule : definition.functionRules().get(kLabelConstant)) {
                    /* function rules should be applied by pattern match rather than unification */
                    Collection<Map<Variable, Term>> solutions = PatternMatcher.patternMatch(kItem, rule, context);
                    if (solutions.isEmpty()) {
                        continue;
                    }

                    Map<Variable, Term> solution = solutions.iterator().next();
                    if (tool == Tool.KOMPILE || javaOptions.concreteExecution()) {
                        assert solutions.size() <= 1 :
                            "[non-deterministic function definition]: more than one way to apply the rule\n"
                            + rule + "\nagainst the function\n" + kItem;
                    }

                    Term rightHandSide = rule.rightHandSide();
                    if (rule.hasUnboundVariables()) {
                        // this opt. only makes sense when using pattern matching
                        // because after unification variables can end up in the
                        // constraint rather than in the form of substitution

                        /* rename unbound variables */
                        Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.unboundVariables());
                        /* rename rule variables in the rule RHS */
                        rightHandSide = rightHandSide.substituteWithBinders(freshSubstitution, context);
                    }
                    if (copyOnShareSubstAndEval) {
                        rightHandSide = rightHandSide.copyOnShareSubstAndEval(
                                solution,
                                rule.reusableVariables().elementSet(),
                                context);
                    } else {
                        rightHandSide = rightHandSide.substituteAndEvaluate(solution, context);
                    }

                    if (rule.containsAttribute("owise")) {
                        /*
                         * YilongL: consider applying ``owise'' rule only when the
                         * function is ground. This is fine because 1) it's OK not
                         * to fully evaluate non-ground function during kompilation;
                         * and 2) it's better to get stuck rather than to apply the
                         * wrong ``owise'' rule during execution.
                         */
                        if (kItem.isGround()) {
                            owiseResults.add(rightHandSide);
                        }
                    } else {
                        if (javaOptions.concreteExecution()) {
                            assert result == null || result.equals(rightHandSide):
                                "[non-deterministic function definition]: more than one rule can apply to the function\n" + kItem;
                        }
                        result = rightHandSide;
                    }

                    /*
                     * If the function definitions do not need to be deterministic, try them in order
                     * and apply the first one that matches.
                     */
                    if (!javaOptions.deterministicFunctions
                            && result != null) {
                        return result;
                    }
                }

                if (result != null) {
                    return result;
                } else if (!owiseResults.isEmpty()) {
                    assert owiseResults.size() == 1 :
                        "[non-deterministic function definition]: more than one ``owise'' rule for the function\n"
                        + kItem;
                    return owiseResults.iterator().next();
                }
            }

            return kItem;
        }
    }

    private boolean isAnywhereApplicable(TermContext context) {
        if (anywhereApplicable != null) {
            return anywhereApplicable;
        }

        anywhereApplicable = (kLabel instanceof KLabelConstant)
                && !context.definition().anywhereRules()
                        .get((KLabelConstant) kLabel).isEmpty();
        return anywhereApplicable;
    }

    /**
     * Apply [anywhere] associated with this {@code KItem}.
     *
     * @param copyOnShareSubstAndEval
     *            specifies whether to use
     *            {@link CopyOnShareSubstAndEvalTransformer} when applying
     *            [anywhere] rules
     *
     * @param context
     *            a term context
     *
     * @return the result on success, or this {@code KItem} otherwise
     */
    private Term applyAnywhereRules(boolean copyOnShareSubstAndEval, TermContext context) {
        if (!isAnywhereApplicable(context)) {
            return this;
        }

        Definition definition = context.definition();
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

        /* apply [anywhere] rules */
        /* TODO(YilongL): make KLabelConstant dependent on Definition and store
         * anywhere rules in KLabelConstant */
        for (Rule rule : definition.anywhereRules().get(kLabelConstant)) {
            /* anywhere rules should be applied by pattern match rather than unification */
            Collection<Map<Variable, Term>> solutions = PatternMatcher.patternMatch(this, rule, context);
            if (solutions.isEmpty()) {
                continue;
            } else {
                Map<Variable, Term> solution = solutions.iterator().next();
                Term rightHandSide = rule.rightHandSide();
                if (copyOnShareSubstAndEval) {
                    rightHandSide = rightHandSide.copyOnShareSubstAndEval(
                            solution,
                            rule.reusableVariables().elementSet(),
                            context);
                } else {
                    rightHandSide = rightHandSide.substituteAndEvaluate(solution, context);
                }
                return rightHandSide;
            }
        }

        return this;
    }

    public Term kLabel() {
        return kLabel;
    }

    public Term kList() {
        return kList;
    }

    @Override
    public boolean isExactSort() {
        return isExactSort;
    }

    /**
     * A {@code KItem} cannot be further decomposed in a unification task if and
     * only if its {@code KLabel} represents a function.
     */
    @Override
    public boolean isSymbolic() {
        // TODO(AndreiS): handle KLabel variables
        //return !(kLabel instanceof KLabel) || ((KLabel) kLabel).isFunction();
        return kLabel instanceof KLabel
                && (((KLabel) kLabel).isFunction() || ((KLabel) kLabel).isPattern());
    }

    @Override
    public Sort sort() {
        return sort;
    }

    /**
     * @return a unmodifiable view of the possible minimal sorts of this
     *         {@code KItem} when its {@code KLabel} is a constructor;
     *         otherwise, null;
     */
    public Set<Sort> possibleMinimalSorts() {
        // TODO(YilongL): reconsider the use of this method when doing test generation
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KItem)) {
            return false;
        }

        KItem kItem = (KItem) object;
        return kLabel.equals(kItem.kLabel) && kList.equals(kItem.kList);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + kLabel.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + kList.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        return kLabel.isMutable() || kList.isMutable();
    }

    @Override
    public String toString() {
        return kLabel + "(" + kList.toString() + ")";
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    public Term expandPattern(SymbolicConstraint constraint, boolean narrowing, TermContext context) {
        if (constraint == null) {
            return this;
        }

        if (!(kLabel instanceof KLabelConstant && ((KLabelConstant) kLabel).isPattern() && kList instanceof KList)) {
            return this;
        }
        KLabelConstant kLabel = (KLabelConstant) kLabel();
        KList kList = (KList) kList();

        List<ConstrainedTerm> results = new ArrayList<>();
        Term inputKList = KList.concatenate(getPatternInput());
        Term outputKList = KList.concatenate(getPatternOutput());
        for (Rule rule : context.definition().patternRules().get(kLabel)) {
            Term ruleInputKList = KList.concatenate(((KItem) rule.leftHandSide()).getPatternInput());
            Term ruleOutputKList = KList.concatenate(((KItem) rule.leftHandSide()).getPatternOutput());
            SymbolicConstraint unificationConstraint = new SymbolicConstraint(context);
            unificationConstraint.add(inputKList, ruleInputKList);
            unificationConstraint.simplify();
            // TODO(AndreiS): there is only one solution here, so no list of constraints
            if (unificationConstraint.isFalse()) {
                continue;
            }

            if (narrowing) {
                SymbolicConstraint globalConstraint = SymbolicConstraint.simplifiedConstraintFrom(context,
                                constraint.equalities(),
                                unificationConstraint,
                                rule.requires());
                if (globalConstraint.isFalse() || globalConstraint.checkUnsat()) {
                    continue;
                }
            } else {
                if (!unificationConstraint.isMatching(ruleInputKList.variableSet())) {
                    continue;
                }

                SymbolicConstraint requires = SymbolicConstraint
                        .simplifiedConstraintFrom(context, rule.requires(), unificationConstraint);
                requires.orientSubstitution(ruleInputKList.variableSet());
                if (requires.isFalse() || !constraint.implies(requires, ruleInputKList.variableSet())) {
                    continue;
                }
            }

            unificationConstraint.add(outputKList, ruleOutputKList);
            unificationConstraint.addAllThenSimplify(rule.ensures());
            if (!unificationConstraint.isFalse() && !unificationConstraint.checkUnsat()) {
                results.add(SymbolicRewriter.constructNewSubjectTerm(
                        rule,
                        unificationConstraint,
                        variableSet()));
            }
        }

        if (results.size() == 1) {
            /* TODO(YilongL): this seems problematic since it modifies the
             * outside constraint while SymbolicConstraint#expandPatterns is
             * still traversing it */
            constraint.addAll(results.get(0).constraint());
            return results.get(0).term().expandPatterns(constraint, narrowing, context);
        } else {
            return this;
        }
    }

    public List<Term> getPatternInput() {
        assert kLabel instanceof KLabelConstant && ((KLabelConstant) kLabel).isPattern() && kList instanceof KList;
        int inputCount = Integer.parseInt(
                ((KLabelConstant) kLabel).productions().get(0).getAttribute(Attribute.PATTERN_KEY));
        return ((KList) kList).getContents().subList(0, inputCount);
    }

    public List<Term> getPatternOutput() {
        assert kLabel instanceof KLabelConstant && ((KLabelConstant) kLabel).isPattern() && kList instanceof KList;
        int inputCount = Integer.parseInt(
                ((KLabelConstant) kLabel).productions().get(0).getAttribute(Attribute.PATTERN_KEY));
        return ((KList) kList).getContents().subList(inputCount, ((KList) kList).getContents().size());
    }

    /**
     * The sort information of this {@code KItem}, namely {@link KItem#sort} and
     * {@link KItem#isExactSort}, depends only on the {@code KLabelConstant} and
     * the sorts of its children.
     */
    private static final class CacheTableColKey {

        final KLabelConstant kLabelConstant;
        final Sort[] sorts;
        final boolean[] bools;
        final int hashCode;

        public CacheTableColKey(KLabelConstant kLabelConstant, KList kList) {
            this.kLabelConstant = kLabelConstant;
            sorts = new Sort[kList.concreteSize()];
            bools = new boolean[kList.concreteSize()];
            int idx = 0;
            for (Term term : kList) {
                if (term instanceof KItem){
                    KItem kItem = (KItem) term;
                    if (kItem.kLabel instanceof KLabelInjection) {
                        term = ((KLabelInjection) kItem.kLabel).term();
                    }
                }
                sorts[idx] = term.sort();
                bools[idx] = term.isExactSort();
                idx++;
            }
            hashCode = computeHash();
        }

        private int computeHash() {
            int hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + kLabelConstant.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + Arrays.deepHashCode(sorts);
            hashCode = hashCode * Utils.HASH_PRIME + Arrays.hashCode(bools);
            return hashCode;
        }

        @Override
        public int hashCode() {
            return hashCode;
        }

        @Override
        public boolean equals(Object object) {
            if (!(object instanceof CacheTableColKey)) {
                return false;
            }
            CacheTableColKey key = (CacheTableColKey) object;
            return kLabelConstant.equals(key.kLabelConstant)
                    && Arrays.deepEquals(sorts, key.sorts)
                    && Arrays.equals(bools, key.bools);
        }
    }

    private static final class CacheTableValue {

        final Sort sort;
        final boolean isExactSort;

        CacheTableValue(Sort sort, boolean isExactSort) {
            this.sort = sort;
            this.isExactSort = isExactSort;
        }
    }

}

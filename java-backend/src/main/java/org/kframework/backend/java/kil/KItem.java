// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.Sets;
import com.google.inject.Provider;
import org.kframework.attributes.Att;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.RuleAuditing;
import org.kframework.backend.java.symbolic.Stage;
import org.kframework.backend.java.symbolic.Substitution;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.backend.java.util.ImpureFunctionException;
import org.kframework.backend.java.util.Profiler;
import org.kframework.backend.java.util.RewriteEngineUtils;
import org.kframework.backend.java.util.RuleSourceUtil;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.backend.java.utils.BitSet;
import org.kframework.builtin.KLabels;
import org.kframework.kil.Attribute;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Represents a K application which applies a {@link KLabel} to a {@link KList}.
 * Or in the usual syntax of K, it can be defined as the following:
 * <p>
 * <blockquote>
 * <p>
 * <pre>
 * syntax KItem ::= KLabel "(" KList ")"
 * </pre>
 * <p>
 * </blockquote>
 * <p>
 *
 * @author AndreiS
 */
@SuppressWarnings("serial")
public class KItem extends Term implements KItemRepresentation {

    private final Term kLabel;
    private final Term kList;

    // sort info, computed lazily
    private boolean isExactSort;
    private Sort sort;
    private Set<Sort> possibleSorts;
    private transient boolean enableCache; // for lazy computation
    private final GlobalContext global; // for lazy computation

    private Boolean evaluable = null;
    private Boolean anywhereApplicable = null;

    private BitSet[] childrenDontCareRuleMask = null;

    public static KItem of(Term kLabel, Term kList, GlobalContext global) {
        return of(kLabel, kList, global, Att.empty(), null);
    }

    public static KItem of(Term kLabel, KList kList, GlobalContext global, BitSet[] childrenDontCareRuleMask) {
        return of(kLabel, kList, global, Att.empty(), childrenDontCareRuleMask);
    }

    public static KItem of(Term kLabel, Term kList, GlobalContext global, Att att) {
        return of(kLabel, kList, global, att, null);
    }

    public static KItem of(Term kLabel, Term kList, GlobalContext global, Att att, BitSet[] childrenDontCareRuleMask) {
        /* YilongL: since KList.Builder always canonicalizes its result, the
         * following conversion is necessary */
        kList = KCollection.upKind(kList, Kind.KLIST);

        // TODO(yilongli): break the dependency on the Tool object
        return new KItem(kLabel, kList, global, global.stage, att, childrenDontCareRuleMask);
    }

    public KItem(KLabel kLabel, Term kList, GlobalContext global, Sort sort, boolean isExactSort, Att att) {
        this(kLabel, kList, global, sort, isExactSort, Collections.singleton(sort), att);
    }

    public KItem(Term kLabel, Term kList, GlobalContext global, Sort sort, boolean isExactSort) {
        this(kLabel, kList, global, sort, isExactSort, null, null);
    }

    private KItem(Term kLabel, Term kList, GlobalContext global, Sort sort, boolean isExactSort, Set<Sort> possibleSorts, Att att) {
        super(computeKind(kLabel), att);
        this.kLabel = kLabel;
        this.kList = kList;
        this.sort = sort;
        this.isExactSort = isExactSort;
        this.possibleSorts = possibleSorts;
        this.global = global;
        this.enableCache = false;
    }

    private KItem(Term kLabel, Term kList, GlobalContext global, Stage stage, Att att, BitSet[] childrenDonCareRuleMask) {
        super(computeKind(kLabel), att);
        this.kLabel = kLabel;
        this.kList = kList;
        this.global = global;

        Definition definition = global.getDefinition();
        this.childrenDontCareRuleMask = childrenDonCareRuleMask;

        if (kLabel instanceof KLabelConstant && kList instanceof KList
                && !((KList) kList).hasFrame()) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

            /* at runtime, checks if the result has been cached */
            enableCache = (stage == Stage.REWRITING)
                    && definition.sortPredicateRulesOn(kLabelConstant).isEmpty();

            sort = null;
            isExactSort = false;
            possibleSorts = null;
        } else {
            /* not a KLabelConstant or the kList contains a frame variable */
            if (kLabel instanceof KLabelInjection) {
                assert kList.equals(KList.EMPTY);
                isExactSort = true;
            } else {
                isExactSort = false;
            }

            sort = kind.asSort();
            possibleSorts = Collections.singleton(sort);
            enableCache = false;
        }
    }

    private static Kind computeKind(Term kLabel) {
        if (kLabel instanceof KLabelConstant) {
            org.kframework.kore.KLabel name = ((KLabelConstant) kLabel);
            if (KLabels.DOTK.equals(name) || KLabels.KSEQ.equals(name)) {
                return Kind.K;
            }
        }
        return Kind.KITEM;
    }

    private void computeSort() {
        if (sort != null) {
            return;
        }

        Definition definition = global.getDefinition();
        if (enableCache) {
            CacheTableColKey cacheTabColKey = new CacheTableColKey((KLabelConstant) kLabel, (KList) kList);
            CacheTableValue cacheTabVal = definition.getSortCacheValue(cacheTabColKey);
            if (cacheTabVal != null) {
                sort = cacheTabVal.sort;
                isExactSort = cacheTabVal.isExactSort;
                possibleSorts = cacheTabVal.possibleSorts;
                return;
            }
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
        KList kList = (KList) this.kList;
        Subsorts subsorts = definition.subsorts();

        Set<Sort> sorts = Sets.newHashSet();
        Set<Sort> possibleSorts = Sets.newHashSet();

        /*
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
            TermContext context = TermContext.builder(global).build();
            if (MetaK.matchable(kList, rule.sortPredicateArgument().kList(), context)
                    .equals(BoolToken.TRUE)) {
                sorts.add(rule.predicateSort());
            } else if (BoolToken.TRUE.equals(MetaK.unifiable(
                    kList, rule.sortPredicateArgument().kList(), context))) {
                possibleSorts.add(rule.predicateSort());
            }
        }

        for (SortSignature signature : kLabelConstant.signatures()) {
            boolean mustMatch = true;
            boolean mayMatch = true;

            if (kList.concreteSize() == signature.parameters().size()) {
                /* check if the production can match this KItem */
                int idx = 0;
                for (Term term : kList) {
                    if (!mayMatch) {
                        break;
                    }

                    Sort childSort = term.sort();
                    if (!definition.subsorts().isSubsortedEq(signature.parameters().get(idx), childSort)) {
                        mustMatch = false;
                        /*
                         * YilongL: the following analysis can be made more
                         * precise by considering all possible sorts of the
                         * term; however, it would be too expensive to
                         * compute for our purpose
                         */
                        mayMatch = !term.isExactSort()
                                && definition.subsorts().hasCommonSubsort(signature.parameters().get(idx), childSort);
                    }
                    idx++;
                }
            } else {
                mustMatch = mayMatch = false;
            }

            if (mustMatch) {
                sorts.add(signature.result());
            } else if (mayMatch) {
                possibleSorts.add(signature.result());
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
            throw KEMException.criticalError("Cannot compute least sort of term: " + this.toString() + ".\n"
                    + "Possible sorts are " + sorts + "\n."
                    + "All terms must have a unique least sort; "
                    + "consider assigning unique KLabels to overloaded productions.", this);
        }
        if (!sorts.isEmpty() && !sorts.contains(sort)) {
            throw KEMException.criticalError("Cannot compute least sort of term: " + this.toString() + ".\n"
                    + "Possible sorts are " + sorts + ", but their least common subsort is " + sort + ", which is not a possible sort."
                    + "All terms must have a unique least sort; "
                    + "consider assigning unique KLabels to overloaded productions/completing the subsort lattice.", this);
        }
        /* the sort is exact iff the klabel is a constructor and there is no other possible sort */
        boolean isExactSort = kLabelConstant.isConstructor() && possibleSorts.isEmpty();
        possibleSorts.add(sort);

        this.sort = sort;
        this.isExactSort = isExactSort;
        this.possibleSorts = possibleSorts;

        CacheTableValue cacheTabVal = new CacheTableValue(sort, isExactSort, possibleSorts);

        if (enableCache) {
            definition.putSortCacheValue(new CacheTableColKey(kLabelConstant, kList), cacheTabVal);
        }
    }

    public boolean isEvaluable() {
        return global.kItemOps.isEvaluable(this, global.getDefinition());
    }

    public Term evaluateFunction(TermContext context) {
        global.profiler.resFuncNanoTimer.start();
        Term result;
        try {
            if (global.javaExecutionOptions.cacheFunctions && isPure()) {
                ConjunctiveFormula constraint = getCacheConstraint(context);
                result = cacheGet(constraint);
                if (result == null) {
                    result = global.kItemOps.evaluateFunction(this, context);
                    result.cachePut(constraint, result);
                    this.cachePut(constraint, result);
                }
            } else {
                result = global.kItemOps.evaluateFunction(this, context);
            }
        } finally {
            global.profiler.resFuncNanoTimer.stop();
        }
        return result;
    }

    public Term resolveFunctionAndAnywhere(TermContext context) {
        global.profiler.resFuncNanoTimer.start();
        Term result;
        try {
            if (global.javaExecutionOptions.cacheFunctions && isPure()) {
                ConjunctiveFormula constraint = getCacheConstraint(context);
                result = cacheGet(constraint);
                if (result == null) {
                    result = global.kItemOps.resolveFunctionAndAnywhere(this, context);
                    result.cachePut(constraint, result);
                    this.cachePut(constraint, result);
                }
            } else {
                result = global.kItemOps.resolveFunctionAndAnywhere(this, context);
            }
        } finally {
            global.profiler.resFuncNanoTimer.stop();
        }
        return result;
    }

    @Override
    public Term toKore() {
        return this;
    }

    /**
     * @param i
     * @return the rules for which position i only matches "don't care" variables (i.e., variables that do not appear
     * in the RHS or conditions)
     */
    public BitSet getChildrenDontCareRuleMaskForPosition(int i) {
        if (childrenDontCareRuleMask != null)
            return childrenDontCareRuleMask[i];
        else
            return null;
    }

    public static class KItemOperations {

        private final Stage stage;
        private final boolean deterministicFunctions;
        private final KExceptionManager kem;
        private final Provider<BuiltinFunction> builtins;
        private final GlobalOptions options;

        public KItemOperations(
                Stage stage,
                boolean deterministicFunctions,
                KExceptionManager kem,
                Provider<BuiltinFunction> builtins,
                GlobalOptions options) {
            this.stage = stage;
            this.deterministicFunctions = deterministicFunctions;
            this.kem = kem;
            this.builtins = builtins;
            this.options = options;
        }

        private static final String TRACE_MSG = "Function evaluation triggered infinite recursion. Trace:";

        /**
         * Evaluates this {@code KItem} if it is a predicate or function; otherwise,
         * applies [anywhere] rules associated with this {@code KItem}
         *
         * @param context                 a term context
         * @return the reduced result on success, or this {@code KItem} otherwise
         */
        public Term resolveFunctionAndAnywhere(KItem kItem, TermContext context) {
            try {
                Term result = kItem.isEvaluable() ? evaluateFunction(kItem, context) : kItem.applyAnywhereRules(context);
                if (result instanceof KItem && ((KItem) result).isEvaluable() && result.isGround()) {
                    // we do this check because this warning message can be very large and cause OOM
                    if (options.warnings.includesExceptionType(ExceptionType.HIDDENWARNING) && stage == Stage.REWRITING) {
                        StringBuilder sb = new StringBuilder();
                        sb.append("Unable to resolve function symbol:\n\t\t");
                        sb.append(result);
                        sb.append('\n');
                        if (!context.definition().functionRules().isEmpty()) {
                            sb.append("\tDefined function rules:\n");
                            for (Rule rule : context.definition().functionRules().get((KLabelConstant) ((KItem) result).kLabel())) {
                                sb.append("\t\t");
                                sb.append(rule);
                                sb.append('\n');
                            }
                        }
                        kem.registerInternalHiddenWarning(sb.toString(), kItem);
                    }
                    if (RuleAuditing.isAuditBegun()) {
                        System.err.println("Function failed to evaluate: returned " + result);
                    }
                }
                return result;
            } catch (StackOverflowError e) {
                throw KEMException.criticalError(TRACE_MSG, e);
            } catch (KEMException e) {
                e.exception.addTraceFrame("while evaluating function " + kItem.kLabel().toString());
                throw e;
            }
        }

        public boolean isEvaluable(KItem kItem, Definition definition) {
            if (kItem.evaluable != null) {
                return kItem.evaluable;
            }

            kItem.evaluable = false;
            if (!(kItem.kLabel instanceof KLabelConstant)) {
                return false;
            }
            KLabelConstant kLabelConstant = (KLabelConstant) kItem.kLabel;

            if (!(kItem.kList instanceof KList)) {
                return false;
            }

            if (kLabelConstant.isSortPredicate()
                    || !definition.functionRules().get(kLabelConstant).isEmpty()
                    || builtins.get().isBuiltinKLabel(kLabelConstant)) {
                kItem.evaluable = true;
            }
            return kItem.evaluable;
        }

        /**
         * Evaluates this {@code KItem} if it is a predicate or function
         *
         * @param context                 a term context
         * @return the evaluated result on success, or this {@code KItem} otherwise
         */
        public Term evaluateFunction(KItem kItem, TermContext context) {
            if (!kItem.isEvaluable()) {
                return kItem;
            }

            Definition definition = context.definition();
            KLabelConstant kLabelConstant = (KLabelConstant) kItem.kLabel;

            Profiler.startTimer(Profiler.getTimerForFunction(kLabelConstant));

            try {
                KList kList = (KList) kItem.kList;

                if (builtins.get().isBuiltinKLabel(kLabelConstant)) {
                    try {
                        Term[] arguments = kList.getContents().toArray(new Term[kList.getContents().size()]);
                        Term result = builtins.get().invoke(context, kLabelConstant, arguments);
                        if (result != null && !result.equals(kItem)) {
                            return result.evaluate(context);
                        }
                    } catch (ClassCastException e) {
                        // DISABLE EXCEPTION CHECKSTYLE
                    } catch (ImpureFunctionException e) {
                        // do not do anything further: immediately assume this function is not ready to be evaluated yet.
                        return kItem;
                    } catch (Throwable t) {
                        // ENABLE EXCEPTION CHECKSTYLE
                        if (t instanceof Error) {
                            throw (Error) t;
                        }
                        if (t instanceof KEMException) {
                            throw (RuntimeException) t;
                        }
                        if (t instanceof RuntimeException) {
                            kem.registerInternalWarning("Ignored exception thrown by hook " + kLabelConstant, t);
                        } else {
                            throw new AssertionError("Builtin functions should not throw checked exceptions", t);
                        }
                    }
                }

                /* evaluate a sort membership predicate */
                // TODO(YilongL): maybe we can move sort membership evaluation after
                // applying user-defined rules to allow the users to provide their
                // own rules for checking sort membership
                if (kLabelConstant.isSortPredicate() && kList.getContents().size() == 1) {
                    Term checkResult = SortMembership.check(kItem, definition);
                    if (checkResult != kItem) {
                        return checkResult;
                    }
                }

                /* apply rules for user defined functions */
                if (!definition.functionRules().get(kLabelConstant).isEmpty()) {
                    Term result = null;
                    Term owiseResult = null;
                    Rule appliedRule = null;

                    // an argument is concrete if it doesn't contain variables or unresolved functions
                    boolean isConcrete = kList.getContents().stream().filter(elem -> !elem.isGround() || !elem.isNormal()).collect(Collectors.toList()).isEmpty();
                    for (Rule rule : definition.functionRules().get(kLabelConstant)) {
                        try {
                            if (rule == RuleAuditing.getAuditingRule()) {
                                RuleAuditing.beginAudit();
                            } else if (RuleAuditing.isAuditBegun() && RuleAuditing.getAuditingRule() == null) {
                                System.err.println("\nAuditing " + rule + "...\n");
                            }

                            // a concrete rule is skipped if some argument is not concrete
                            if (rule.isConcrete() && !isConcrete) {
                                continue;
                            }

                            Substitution<Variable, Term> solution;
                            List<Substitution<Variable, Term>> matches = PatternMatcher.match(kItem, rule, context);
                            if (matches.isEmpty()) {
                                continue;
                            } else {
                                if (matches.size() > 1) {
                                    if (deterministicFunctions) {
                                        throw KEMException.criticalError("More than one possible match. " +
                                                "Function " + kLabelConstant + " might be non-deterministic.");
                                    }
                                    kem.registerInternalWarning("More than one possible match. " +
                                            "Behaviors might be lost.");
                                }
                                solution = matches.get(0);
                            }

                            /* rename fresh variables of the rule */
                            for (Variable freshVar : rule.variableSet()) {
                                if (!solution.containsKey(freshVar)) {
                                    solution = solution.plus(freshVar, freshVar.getFreshCopy());
                                }
                            }
                            Term rightHandSide = RewriteEngineUtils.construct(
                                    rule.rhsInstructions(),
                                    solution,
                                    context);

                            if (rule.att().contains("owise")) {
                                if (owiseResult != null) {
                                    throw KEMException.criticalError("Found multiple [owise] rules for the function with KLabel " + kItem.kLabel, rule);
                                }
                                RuleAuditing.succeed(rule);
                                owiseResult = rightHandSide;
                            } else {
                                if (stage == Stage.REWRITING) {
                                    if (deterministicFunctions && result != null && !result.equals(rightHandSide)) {
                                        StringBuffer sb = new StringBuffer();
                                        sb.append("[non-deterministic function definition]: more than one rule can apply to the term: \n").append(kItem);
                                        sb.append("\n\nCandidate rules:\n");
                                        RuleSourceUtil.appendRuleAndSource(appliedRule, sb);
                                        RuleSourceUtil.appendRuleAndSource(rule, sb);
                                        sb.append("\n\nCandidate results:\n");
                                        sb.append(result).append("\n");
                                        sb.append(rightHandSide).append("\n");
                                        throw KEMException.criticalError(sb.toString());
                                    }
                                }
                                RuleAuditing.succeed(rule);
                                result = rightHandSide;
                                appliedRule = rule;
                            }

                            /*
                             * If the function definitions do not need to be deterministic, try them in order
                             * and apply the first one that matches.
                             */
                            if (!deterministicFunctions && result != null) {
                                return result;
                            }
                        } finally {
                            if (RuleAuditing.isAuditBegun()) {
                                if (RuleAuditing.getAuditingRule() == rule) {
                                    RuleAuditing.endAudit();
                                }
                                if (!RuleAuditing.isSuccess()
                                        && RuleAuditing.getAuditingRule() == rule) {
                                    throw RuleAuditing.fail();
                                }
                            }
                        }
                    }

                    if (result != null) {
                        return result;
                    } else if (owiseResult != null) {
                        if (!kItem.isGround()) {
                            if (context.global().stage != Stage.REWRITING) {
                                return kItem;
                            }

                            /*
                             * apply the "[owise]" rule only if this kItem does not unify with any
                             * of the left-hand-sides of the other rules (no other rule may apply)
                             */
                            for (Rule rule : definition.functionRules().get(kLabelConstant)) {
                                if (rule.att().contains("owise")) {
                                    continue;
                                }

                                ConstrainedTerm subject = new ConstrainedTerm(
                                        kItem.kList(),
                                        context);
                                ConstrainedTerm pattern = new ConstrainedTerm(
                                        ((KItem) rule.leftHandSide()).kList(),
                                        ConjunctiveFormula.of(context.global())
                                                .add(rule.lookups())
                                                .addAll(rule.requires()),
                                        context);
                                if (!subject.unify(pattern, null).isEmpty()) {
                                    return kItem;
                                }
                            }
                        }
                        return owiseResult;
                    }
                }
                return kItem;
            } finally {
                Profiler.stopTimer(Profiler.getTimerForFunction(kLabelConstant));
            }
        }
    }

    public boolean isAnywhereApplicable(TermContext context) {
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
     * @param context                 a term context
     * @return the result on success, or this {@code KItem} otherwise
     */
    public Term applyAnywhereRules(TermContext context) {
        // apply a .K ~> K => K normalization
        if ((kLabel instanceof KLabelConstant) && KLabels.KSEQ.equals(kLabel)
                && kList instanceof KList
                && (((KList) kList).get(0) instanceof KItem && KLabels.DOTK.equals(((KItem) ((KList) kList).get(0)).kLabel) || ((KList) kList).get(0).equals(KSequence.EMPTY))) {
            return ((KList) kList).get(1);
        }

        if (!isAnywhereApplicable(context)) {
            return this;
        }

        Definition definition = context.definition();
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

        /* apply [anywhere] rules */
        /* TODO(YilongL): make KLabelConstant dependent on Definition and store
         * anywhere rules in KLabelConstant */
        for (Rule rule : definition.anywhereRules().get(kLabelConstant)) {
            try {
                if (rule == RuleAuditing.getAuditingRule()) {
                    RuleAuditing.beginAudit();
                } else if (RuleAuditing.isAuditBegun() && RuleAuditing.getAuditingRule() == null) {
                    System.err.println("\nAuditing " + rule + "...\n");
                }
                /* anywhere rules should be applied by pattern match rather than unification */
                Map<Variable, Term> solution;
                List<Substitution<Variable, Term>> matches = PatternMatcher.match(this, rule, context);
                if (matches.isEmpty()) {
                    continue;
                } else {
                    assert matches.size() == 1 : "unexpected non-deterministic anywhere rule " + rule;
                    solution = matches.get(0);
                }

                RuleAuditing.succeed(rule);
                Term rightHandSide = rule.rightHandSide();
                rightHandSide = rightHandSide.substituteAndEvaluate(solution, context);
                return rightHandSide;
            } finally {
                if (RuleAuditing.isAuditBegun()) {
                    if (RuleAuditing.getAuditingRule() == rule) {
                        RuleAuditing.endAudit();
                    }
                    if (!RuleAuditing.isSuccess()
                            && RuleAuditing.getAuditingRule() == rule) {
                        throw RuleAuditing.fail();
                    }
                }
            }
        }

        return this;
    }

    @Override
    public Term kLabel() {
        return kLabel;
    }

    @Override
    public Term kList() {
        return kList;
    }

    public GlobalContext globalContext() {
        return global;
    }

    @Override
    public boolean isExactSort() {
        computeSort();
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
        computeSort();
        return sort;
    }

    public Set<Sort> possibleSorts() {
        computeSort();
        return Collections.unmodifiableSet(possibleSorts);
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
        hashCode = hashCode * Constants.HASH_PRIME + kLabel.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + kList.hashCode();
        return hashCode;
    }

    @Override
    public String toString() {
        return kLabel + "(" + kList.toString() + ")";
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    public List<Term> getPatternInput() {
        assert kLabel instanceof KLabelConstant && ((KLabelConstant) kLabel).isPattern() && kList instanceof KList;
        int inputCount = Integer.parseInt(((KLabelConstant) kLabel).getAttr(Attribute.PATTERN_KEY));
        return ((KList) kList).getContents().subList(0, inputCount);
    }

    public List<Term> getPatternOutput() {
        assert kLabel instanceof KLabelConstant && ((KLabelConstant) kLabel).isPattern() && kList instanceof KList;
        int inputCount = Integer.parseInt(((KLabelConstant) kLabel).getAttr(Attribute.PATTERN_KEY));
        return ((KList) kList).getContents().subList(inputCount, ((KList) kList).getContents().size());
    }

    /**
     * The sort information of this {@code KItem}, namely {@link KItem#sort} and
     * {@link KItem#isExactSort}, depends only on the {@code KLabelConstant} and
     * the sorts of its children.
     */
    static final class CacheTableColKey {

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
                if (term instanceof KItem) {
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
            hashCode = hashCode * Constants.HASH_PRIME + kLabelConstant.hashCode();
            hashCode = hashCode * Constants.HASH_PRIME + Arrays.deepHashCode(sorts);
            hashCode = hashCode * Constants.HASH_PRIME + Arrays.hashCode(bools);
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

    /**
     * When serializing a KItem, compute its sort so that we don't end up serializing the TermContext
     *
     * @param out
     * @throws IOException
     */
    private void writeObject(ObjectOutputStream out) throws IOException {
        computeSort();
        out.defaultWriteObject();
    }

    static final class CacheTableValue {

        final Sort sort;
        final boolean isExactSort;
        final Set<Sort> possibleSorts;

        CacheTableValue(Sort sort, boolean isExactSort, Set<Sort> possibleSorts) {
            this.sort = sort;
            this.isExactSort = isExactSort;
            this.possibleSorts = possibleSorts;
        }
    }

}

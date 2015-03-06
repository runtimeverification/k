// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.NonACPatternMatcher;
import org.kframework.backend.java.symbolic.RuleAuditing;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.ImpureFunctionException;
import org.kframework.backend.java.util.Profiler;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.*;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;

import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.Sets;
import com.google.inject.Inject;
import com.google.inject.Provider;


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
public class KItem extends Term implements KItemRepresentation {

    private final Term kLabel;
    private final Term kList;

    // sort info, computed lazily
    private boolean isExactSort;
    private Sort sort;
    private Set<Sort> possibleSorts;
    private transient boolean enableCache; // for lazy computation
    private transient TermContext termContext; // for lazy computation

    private Boolean evaluable = null;
    private Boolean anywhereApplicable = null;

    public static KItem of(Term kLabel, Term kList, TermContext termContext) {
           return of(kLabel, kList, termContext, null, null);
    }

    public static KItem of(Term kLabel, Term kList, TermContext termContext, Source source, Location location) {
        /* YilongL: since KList.Builder always canonicalizes its result, the
         * following conversion is necessary */
        kList = KCollection.upKind(kList, Kind.KLIST);

        // TODO(yilongli): break the dependency on the Tool object
        return new KItem(kLabel, kList, termContext, termContext.global().kItemOps.tool, source, location);
    }

    public KItem(Term kLabel, Term kList, Sort sort, boolean isExactSort) {
        this(kLabel, kList, sort, isExactSort, Collections.singleton(sort));
    }

    private KItem(Term kLabel, Term kList, Sort sort, boolean isExactSort, Set<Sort> possibleSorts) {
        super(Kind.KITEM);
        this.kLabel = kLabel;
        this.kList = kList;
        this.sort = sort;
        this.isExactSort = isExactSort;
        this.possibleSorts = possibleSorts;
        this.termContext = null;
        this.enableCache = false;
    }

    private KItem(Term kLabel, Term kList, boolean enableCache, TermContext termContext, Source source, Location location) {
        super(Kind.KITEM, source, location);
        this.kLabel = kLabel;
        this.kList = kList;
        this.sort = null;
        this.isExactSort = false;
        this.possibleSorts = null;
        this.termContext = termContext;
        this.enableCache = enableCache;
    }

    private KItem(Term kLabel, Term kList, TermContext termContext, Tool tool, Source source, Location location) {
        super(Kind.KITEM, source, location);
        this.kLabel = kLabel;
        this.kList = kList;

        Definition definition = termContext.definition();

        if (kLabel instanceof KLabelConstant && kList instanceof KList
                && !((KList) kList).hasFrame()) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

            /* at runtime, checks if the result has been cached */
            CacheTableColKey cacheTabColKey = null;
            CacheTableValue cacheTabVal = null;
            enableCache = (tool != Tool.KOMPILE)
                    && definition.sortPredicateRulesOn(kLabelConstant).isEmpty();
            if (enableCache) {
                cacheTabColKey = new CacheTableColKey(kLabelConstant, (KList) kList);
                cacheTabVal = definition.getSortCacheValue(cacheTabColKey);
                if (cacheTabVal != null) {
                    sort = cacheTabVal.sort;
                    isExactSort = cacheTabVal.isExactSort;
                    possibleSorts = cacheTabVal.possibleSorts;
                    this.termContext = null;
                    return;
                }
            }

            sort = null;
            isExactSort = false;
            possibleSorts = null;
            this.termContext = termContext;
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
            this.termContext = null;
            enableCache = false;
        }
    }

    private void computeSort() {
        if (sort != null) {
            //computed already
            return;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
        KList kList = (KList) this.kList;
        Definition definition = termContext.definition();
        Subsorts subsorts = definition.subsorts();

        Set<Sort> sorts = Sets.newHashSet();
        Set<Sort> possibleSorts = Sets.newHashSet();

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
            throw KExceptionManager.criticalError("Cannot compute least sort of term: " +
                            this.toString() + "\nPossible least sorts are: " + sorts +
                            "\nAll terms must have a unique least sort; " +
                            "consider assigning unique KLabels to overloaded productions", this);
        }
        /* the sort is exact iff the klabel is a constructor and there is no other possible sort */
        boolean isExactSort = kLabelConstant.isConstructor() && possibleSorts.isEmpty();
        possibleSorts.add(sort);

        this.sort = sort;
        this.isExactSort = isExactSort;
        this.possibleSorts = possibleSorts;

        CacheTableValue cacheTabVal = new CacheTableValue(sort, isExactSort, possibleSorts);

        if (enableCache) {
            definition.putSortCacheValue(new CacheTableColKey(kLabelConstant, (KList) kList), cacheTabVal);
        }
    }

    public boolean isEvaluable(TermContext context) {
        return context.global().kItemOps.isEvaluable(this, context);
    }

    public Term evaluateFunction(boolean copyOnShareSubstAndEval, TermContext context) {
        return context.global().kItemOps.evaluateFunction(this, copyOnShareSubstAndEval, context);
    }

    public Term resolveFunctionAndAnywhere(boolean copyOnShareSubstAndEval, TermContext context) {
        return context.global().kItemOps.resolveFunctionAndAnywhere(this, copyOnShareSubstAndEval, context);
    }

    @Override
    public Term toKore() {
        return this;
    }

    public static class KItemOperations {

        private final Tool tool;
        private final JavaExecutionOptions javaOptions;
        private final KExceptionManager kem;
        private final Provider<BuiltinFunction> builtins;
        private final GlobalOptions options;

        @Inject
        public KItemOperations(
                Tool tool,
                JavaExecutionOptions javaOptions,
                KExceptionManager kem,
                Provider<BuiltinFunction> builtins,
                GlobalOptions options) {
            this.tool = tool;
            this.javaOptions = javaOptions;
            this.kem = kem;
            this.builtins = builtins;
            this.options = options;
        }

        private static String TRACE_MSG = "Function evaluation triggered infinite recursion. Trace:";

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
            try {
                Term result = kItem.isEvaluable(context) ?
                        evaluateFunction(kItem, copyOnShareSubstAndEval, context) :
                            kItem.applyAnywhereRules(copyOnShareSubstAndEval, context);
                if (result instanceof KItem && ((KItem) result).isEvaluable(context) && result.isGround()) {
                    // we do this check because this warning message can be very large and cause OOM
                    if (options.warnings.includesExceptionType(ExceptionType.HIDDENWARNING) && tool != Tool.KOMPILE) {
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
                throw KExceptionManager.criticalError(TRACE_MSG, e);
            } catch (KEMException e) {
                e.exception.addTraceFrame("while evaluating function " + kItem.kLabel().toString());
                throw e;
            }
        }

        public boolean isEvaluable(KItem kItem, TermContext context) {
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
                    || !context.definition().functionRules().get(kLabelConstant).isEmpty()
                    || builtins.get().isBuiltinKLabel(kLabelConstant)) {
                kItem.evaluable = true;
            }
            return kItem.evaluable;
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

            Profiler.startTimer(Profiler.getTimerForFunction(kLabelConstant));

            try {
                KList kList = (KList) kItem.kList;

                if (builtins.get().isBuiltinKLabel(kLabelConstant)) {
                    try {
                        Term[] arguments = kList.getContents().toArray(new Term[kList.getContents().size()]);
                        Term result = builtins.get().invoke(context, kLabelConstant, arguments);
                        if (result != null) {
                            return result;
                        }
                    } catch (ClassCastException e) {
                    // DISABLE EXCEPTION CHECKSTYLE
                    } catch (ImpureFunctionException e) {
                        // do not do anything further: immediately assume this function is not ready to be evaluated yet.
                        return kItem;
                    } catch (Throwable t) {
                    // ENABLE EXCEPTION CHECKSTYLE
                        if (t instanceof Error) {
                            throw (Error)t;
                        }
                        if (t instanceof KExceptionManager.KEMException) {
                            throw (RuntimeException)t;
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
                    Term checkResult = SortMembership.check(kItem, context.definition());
                    if (checkResult != kItem) {
                        return checkResult;
                    }
                }

                /* apply rules for user defined functions */
                if (!definition.functionRules().get(kLabelConstant).isEmpty()) {
                    Term result = null;
                    Term owiseResult = null;

                    for (Rule rule : definition.functionRules().get(kLabelConstant)) {
                            try {
                            if (rule == RuleAuditing.getAuditingRule()) {
                                RuleAuditing.beginAudit();
                            } else if (RuleAuditing.isAuditBegun() && RuleAuditing.getAuditingRule() == null) {
                                System.err.println("\nAuditing " + rule + "...\n");
                            }
                            /* function rules should be applied by pattern match rather than unification */
                            Map<Variable, Term> solution = NonACPatternMatcher.match(kItem, rule, context);
                            if (solution == null) {
                                continue;
                            }

                            Term rightHandSide = rule.rightHandSide();
                            if (!rule.freshVariables().isEmpty()) {
                                // this opt. only makes sense when using pattern matching
                                // because after unification variables can end up in the
                                // constraint rather than in the form of substitution

                                /* rename unbound variables */
                                Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.freshVariables());
                                /* rename rule variables in the rule RHS */
                                rightHandSide = rightHandSide.substituteWithBinders(freshSubstitution, context);
                            }
                            rightHandSide = KAbstractRewriteMachine.construct(rule.rhsInstructions(), solution, copyOnShareSubstAndEval ? rule.reusableVariables().elementSet() : null,
                                        context, false);

                            if (rule.containsAttribute("owise")) {
                                /*
                                 * YilongL: consider applying ``owise'' rule only when the
                                 * function is ground. This is fine because 1) it's OK not
                                 * to fully evaluate non-ground function during kompilation;
                                 * and 2) it's better to get stuck rather than to apply the
                                 * wrong ``owise'' rule during execution.
                                 */
                                if (kItem.isGround()) {
                                    if (owiseResult != null) {
                                        throw KExceptionManager.criticalError("Found multiple [owise] rules for the function with KLabel " + kItem.kLabel, rule);
                                    }
                                    RuleAuditing.succeed(rule);
                                    owiseResult = rightHandSide;
                                }
                            } else {
                                if (tool == Tool.KRUN) {
                                    assert result == null || result.equals(rightHandSide):
                                        "[non-deterministic function definition]: more than one rule can apply to the function\n" + kItem;
                                }
                                RuleAuditing.succeed(rule);
                                result = rightHandSide;
                            }

                            /*
                             * If the function definitions do not need to be deterministic, try them in order
                             * and apply the first one that matches.
                             */
                            if (!javaOptions.deterministicFunctions && result != null) {
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
            try {
                if (rule == RuleAuditing.getAuditingRule()) {
                    RuleAuditing.beginAudit();
                } else if (RuleAuditing.isAuditBegun() && RuleAuditing.getAuditingRule() == null) {
                    System.err.println("\nAuditing " + rule + "...\n");
                }
                /* anywhere rules should be applied by pattern match rather than unification */
                Map<Variable, Term> solution = NonACPatternMatcher.match(this, rule, context);
                if (solution != null) {
                    RuleAuditing.succeed(rule);
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

    /**
     * When serializing a KItem, compute its sort so that we don't end up serializing the TermContext
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

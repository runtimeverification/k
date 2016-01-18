// Copyright (c) 2013-2016 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.base.Stopwatch;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.inject.Inject;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;
import org.kframework.Strategy;
import org.kframework.attributes.Att;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.strategies.TransitionCompositeStrategy;
import org.kframework.backend.java.util.Coverage;
import org.kframework.backend.java.util.JavaKRunState;
import org.kframework.builtin.KLabels;
import org.kframework.kil.ASTNode;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.FindK;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.krun.api.KRunState;
import org.kframework.utils.BitSet;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.rewriter.SearchType;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author AndreiS
 */
public class SymbolicRewriter {

    private final JavaExecutionOptions javaOptions;
    private final TransitionCompositeStrategy strategy;
    private final List<String> transitions;
    private final Stopwatch stopwatch = Stopwatch.createUnstarted();
    private final KOREtoBackendKIL constructor;
    private boolean transition;
    private final Set<ConstrainedTerm> superheated = Sets.newHashSet();
    private final Set<ConstrainedTerm> newSuperheated = Sets.newHashSet();
    private final RuleIndex ruleIndex;
    private final KRunState.Counter counter;
    private final Map<ConstrainedTerm, Set<Rule>> subject2DisabledRules = new HashMap<>();
    private final FastRuleMatcher theFastMatcher;
    private final Definition definition;
    private final BitSet allRuleBits;

    private final boolean useFastRewriting;

    @Inject
    public SymbolicRewriter(GlobalContext global, KompileOptions kompileOptions, JavaExecutionOptions javaOptions,
                            KRunState.Counter counter, KOREtoBackendKIL constructor) {
        this.constructor = constructor;
        this.definition = global.getDefinition();
        this.allRuleBits = BitSet.apply(definition.ruleTable.size());
        this.allRuleBits.makeOnes(definition.ruleTable.size());
        this.javaOptions = javaOptions;
        this.ruleIndex = definition.getIndex();
        this.counter = counter;
        this.strategy = new TransitionCompositeStrategy(kompileOptions.transition);
        this.transitions = kompileOptions.transition;
        this.useFastRewriting = !kompileOptions.experimental.koreProve;
        this.theFastMatcher = new FastRuleMatcher(global, definition.ruleTable.size());
        this.transition = useFastRewriting;
    }

    public KRunState rewrite(ConstrainedTerm constrainedTerm, int bound) {
        stopwatch.start();
        int step = 0;
        List<ConstrainedTerm> results;
        while (step != bound && !(results = computeRewriteStep(constrainedTerm, step, true)).isEmpty()) {
            /* get the first solution */
            constrainedTerm = results.get(0);
            step++;
        }

        ConstrainedTerm afterVariableRename = new ConstrainedTerm(new RenameAnonymousVariables().apply(constrainedTerm.term()), constrainedTerm.termContext());

        KRunState finalState = new JavaKRunState(afterVariableRename, counter, Optional.of(step));

        stopwatch.stop();
        if (afterVariableRename.termContext().global().krunOptions.experimental.statistics) {
            System.err.println("[" + step + ", " + stopwatch + " ]");
        }

        return finalState;
    }

    private List<ConstrainedTerm> computeRewriteStep(ConstrainedTerm constrainedTerm, int step, boolean computeOne) {
        return useFastRewriting ?
                fastComputeRewriteStep(constrainedTerm, computeOne) :
                slowComputeRewriteStep(constrainedTerm, step, computeOne);
    }

    private List<ConstrainedTerm> slowComputeRewriteStep(ConstrainedTerm subject, int step, boolean computeOne) {
        RuleAuditing.setAuditingRule(javaOptions, step, subject.termContext().definition());
        try {
            subject.termContext().setTopTerm(subject.term());
            /* rules that are failed to apply on subject */
            Set<Rule> failedRules = new HashSet<>(subject2DisabledRules.getOrDefault(subject, Collections.emptySet()));
            /* resulting terms after rewriting */
            List<ConstrainedTerm> results = new ArrayList<>();

            // Applying a strategy to a list of rules divides the rules up into
            // equivalence classes of rules. We iterate through these equivalence
            // classes one at a time, seeing which one contains rules we can apply.
            for (strategy.reset(ruleIndex.getRules(subject.term())); strategy.hasNext(); ) {
                transition = strategy.nextIsTransition();
                Set<Rule> rules = new LinkedHashSet<>(strategy.next());
                rules.removeAll(failedRules);

                Map<Rule, List<ConstrainedTerm>> rule2Results;
                if (computeOne) {
                    rule2Results = Collections.emptyMap();
                    for (Rule rule : rules) {
                        List<ConstrainedTerm> terms = computeRewriteStepByRule(subject, rule);
                        if (!terms.isEmpty()) {
                            rule2Results = Collections.singletonMap(rule, terms);
                            results.add(terms.get(0));
                            break;
                        } else {
                            failedRules.add(rule);
                        }
                    }
                } else {
                    rule2Results = rules.stream().collect(
                            Collectors.toMap(r -> r, r -> computeRewriteStepByRule(subject, r),
                                    (u, v) -> u, IdentityHashMap::new));
                    for (Rule rule : rules) {
                        if (rule2Results.get(rule).isEmpty()) {
                            failedRules.add(rule);
                        } else {
                            results.addAll(rule2Results.get(rule));
                        }
                    }
                }

                // If we've found matching results from one equivalence class then
                // we are done, as we can't match rules from two equivalence classes
                // in the same step.
                if (!results.isEmpty()) {
                    /* compute disabled rules for the resulting terms */
                    subject2DisabledRules.remove(subject);
                    rule2Results.forEach((appliedRule, terms) -> {
                        // if the latest applied rule doesn't modify the read cells of a failing rule,
                        // that failing rule is deemed to fail again when applied on the new term
                        Set<Rule> rulesWillFail = failedRules.stream()
                                .filter(failedRule -> failedRule.isCompiledForFastRewriting() &&
                                        appliedRule.isCompiledForFastRewriting() &&
                                        Collections.disjoint(failedRule.readCells(), appliedRule.writeCells()))
                                .collect(Collectors.toSet());
                        terms.forEach(t -> subject2DisabledRules.put(t, rulesWillFail));
                    });
                    break;
                }
            }
            return results;
        } finally {
            RuleAuditing.clearAuditingRule();
        }
    }

    /**
     * This method adds a #STUCK item on the top of the strategy cell of the stuck configuration and returns
     * the resulting configuration. If the configuration already had the #STUCK flag, it returns Optional.empty()
     * to end the rewriting.
     */
    private Optional<ConstrainedTerm> addStuckFlagIfNotThere(ConstrainedTerm subject) {
        Optional<K> theStrategy = ((KApply) subject.term()).klist().stream()
                .filter(t -> t instanceof KApply && ((KApply) t).klabel().name().contains(Strategy.strategyCellName()))
                .findFirst();

        if (!theStrategy.isPresent())
            return Optional.empty();

        K topOfStrategyCell = ((KApply) theStrategy.get()).klist().items().get(0);

        if ((topOfStrategyCell instanceof KApply) && ((KApply) topOfStrategyCell).klabel().name().equals(KLabels.KSEQ)) {
            topOfStrategyCell = ((KApply) topOfStrategyCell).klist().items().get(0);
        }
        boolean isStuck = !(topOfStrategyCell instanceof KApply) ||
                ((KApply) topOfStrategyCell).klabel().name().equals(Att.stuck());


        // if we are stuck (i.e., in this method) and the #STUCK marker is the top of the strategy cell, do nothing
        if (isStuck) {
            return Optional.empty();
        }

        // otherwise, add the #STUCK label to the top of the strategy cell

        Att emptyAtt = Att.apply();

        K stuck = constructor.KApply1(constructor.KLabel(Att.stuck()), constructor.KList(), emptyAtt);
        List<K> items = new LinkedList<K>(((KApply) theStrategy.get()).klist().items());
        items.add(0, stuck);
        K sContent = constructor.KApply1(constructor.KLabel(KLabels.KSEQ), constructor.KList(items), emptyAtt);
        K s = constructor.KApply1(((KApply) theStrategy.get()).klabel(), constructor.KList(sContent), emptyAtt);
        K entireConf = constructor.KApply1(((KApply) subject.term()).klabel(),
                constructor.KList(((KApply) subject.term()).klist().stream().map(k ->
                        k instanceof KApply && ((KApply) k).klabel().name().contains(Strategy.strategyCellName()) ? s : k).collect(Collectors.toList())), emptyAtt);
        return Optional.of(new ConstrainedTerm((Term) entireConf, subject.termContext()));

    }

    private boolean strategyIsRestore(ConstrainedTerm subject) {
        throw new UnsupportedOperationException();
    }

    private boolean strategyIsSave(ConstrainedTerm subject) {
        throw new UnsupportedOperationException();
    }

    private Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term> getRewrites(ConjunctiveFormula constraint) {
        return constraint.equalities().stream()
                .filter(e -> e.leftHandSide() instanceof LocalRewriteTerm)
                .map(Equality::leftHandSide)
                .map(LocalRewriteTerm.class::cast)
                .collect(Collectors.toMap(e -> e.path, e -> e.rewriteRHS));
    }

    private List<ConstrainedTerm> fastComputeRewriteStep(ConstrainedTerm subject, boolean computeOne) {
        List<ConstrainedTerm> results = new ArrayList<>();
        if (definition.automaton == null) {
            return results;
        }
        List<Triple<ConjunctiveFormula, Boolean, Integer>> matches = theFastMatcher.matchRulePattern(
                subject,
                definition.automaton.leftHandSide(),
                allRuleBits,
                computeOne,
                transitions,
                subject.termContext());
        for (Triple<ConjunctiveFormula, Boolean, Integer> triple : matches) {
            Rule rule = definition.ruleTable.get(triple.getRight());
            Substitution<Variable, Term> substitution =
                    rule.containsAttribute(Att.refers_THIS_CONFIGURATION()) ?
                            triple.getLeft().substitution().plus(new Variable(KLabels.THIS_CONFIGURATION, Sort.KSEQUENCE), filterOurStrategyCell(subject.term())) :
                            triple.getLeft().substitution();
            boolean isMatching = triple.getMiddle();
            // start the optimized substitution

            // get a map from AST paths to (fine-grained, inner) rewrite RHSs
            Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term> rewrites = getRewrites(triple.getLeft());

            assert (rewrites.size() > 0);


            Term theNew;
            if (rewrites.size() == 1)
            // use the more efficient implementation if we only have one rewrite
            {
                theNew = buildRHS(subject.term(), substitution, rewrites.keySet().iterator().next(),
                        rewrites.values().iterator().next(), subject.termContext());
            } else {
                theNew = buildRHS(subject.term(), substitution,
                        rewrites.entrySet().stream().map(e -> Pair.of(e.getKey(), e.getValue())).collect(Collectors.toList()),
                        subject.termContext());
            }

            // rename rule variables in the term
            theNew = theNew.substituteWithBinders(Variable.rename(rule.variableSet()));

            if (!isMatching) {
                theNew = theNew.substituteAndEvaluate(substitution, subject.termContext());
            }

            theNew = restoreConfigurationIfNecessary(subject, rule, theNew);

            ConstrainedTerm result = new ConstrainedTerm(theNew, subject.termContext());

            /* TODO(AndreiS): remove this hack for super strictness after strategies work */
            if (rule.containsAttribute(Att.heat()) && transitions.stream().anyMatch(rule::containsAttribute)) {
                newSuperheated.add(result);
            } else if (rule.containsAttribute(Att.cool()) && transitions.stream().anyMatch(rule::containsAttribute) && superheated.contains(subject)) {
                continue;
            }

            results.add(result);
        }

        if (results.isEmpty()) {
            addStuckFlagIfNotThere(subject).ifPresent(results::add);
        }

        return results;
    }

    private Term restoreConfigurationIfNecessary(ConstrainedTerm subject, Rule rule, Term theNew) {
        if (rule.containsAttribute(Att.refers_RESTORE_CONFIGURATION())) {
            K strategyCell = new FindK() {
                public scala.collection.Set<K> apply(KApply k) {
                    if (k.klabel().name().equals(Strategy.strategyCellName()))
                        return org.kframework.Collections.Set(k);
                    else
                        return super.apply(k);
                }
            }.apply(theNew).head();

            K theRestoredBody = new FindK() {
                public scala.collection.Set<K> apply(KApply k) {
                    if (k.klabel().name().equals("#RESTORE_CONFIGURATION"))
                        return org.kframework.Collections.Set(k.klist().items().get(0));
                    else
                        return super.apply(k);
                }
            }.apply(theNew).head();

            strategyCell = (K) ((Term) strategyCell).accept(new CopyOnWriteTransformer() {
                @Override
                public ASTNode transform(KItem kItem) {
                    if (kItem.kLabel() instanceof KLabelConstant && ((KLabelConstant) kItem.kLabel()).name().equals("#RESTORE_CONFIGURATION")) {
                        return BuiltinList.kSequenceBuilder(subject.termContext().global()).build();
                    } else {
                        return super.transform(kItem);
                    }
                }
            });

            theNew = ((Term) theRestoredBody).substituteAndEvaluate(Collections.singletonMap(strategyCellPlaceholder, (Term) strategyCell), subject.termContext());
        }
        return theNew;
    }

    Variable strategyCellPlaceholder = new Variable("STRATEGY_CELL_PLACEHOLDER", Sort.KSEQUENCE);

    private Term filterOurStrategyCell(Term term) {
        return (Term) term.accept(new CopyOnWriteTransformer() {
            @Override
            public ASTNode transform(KItem kItem) {

                if (kItem.kLabel() instanceof KLabelConstant && ((KLabelConstant) kItem.kLabel()).name().equals(Strategy.strategyCellName())) {
                    return strategyCellPlaceholder;
                } else {
                    return super.transform(kItem);
                }
            }
        });
    }

    /**
     * goes down the path on the subject to find the rewrite place, does the substitution, and reconstructs the term
     * on its way up
     */
    private Term buildRHS(Term subject, Substitution<Variable, Term> substitution, scala.collection.immutable.List<Pair<Integer, Integer>> path, Term rhs, TermContext context) {
        if (path.isEmpty()) {
            return rhs.substituteAndEvaluate(substitution, context);
        } else {
            if (subject instanceof KItem) {
                KItem kItemSubject = (KItem) subject;
                List<Term> newContents = new ArrayList<>(((KList) kItemSubject.kList()).getContents());
                newContents.set(path.head().getLeft(), buildRHS(newContents.get(path.head().getLeft()), substitution, (scala.collection.immutable.List<Pair<Integer, Integer>>) path.tail(), rhs, context));
                return KItem.of(kItemSubject.kLabel(), KList.concatenate(newContents), context.global()).applyAnywhereRules(false, context);
            } else if (subject instanceof BuiltinList) {
                BuiltinList builtinListSubject = (BuiltinList) subject;
                List<Term> newContents = new ArrayList<>(builtinListSubject.children);
                newContents.set(path.head().getLeft(), buildRHS(newContents.get(path.head().getLeft()), substitution, (scala.collection.immutable.List<Pair<Integer, Integer>>) path.tail(), rhs, context));
                return BuiltinList
                        .builder(builtinListSubject.sort, builtinListSubject.operatorKLabel, builtinListSubject.unitKLabel, builtinListSubject.globalContext())
                        .addAll(newContents)
                        .build();
            } else {
                throw new AssertionError("unexpected rewrite in subject: " + subject);
            }
        }
    }

    /**
     * goes down each of the the paths on the subject to find the rewrite place, does the substitution,
     * and reconstructs the term on its way up
     */
    private Term buildRHS(Term subject, Substitution<Variable, Term> substitution, List<Pair<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>> rewrites, TermContext context) {
        if (rewrites.size() == 1 && rewrites.get(0).getLeft().isEmpty()) {
            return rewrites.get(0).getRight().substituteAndEvaluate(substitution, context);
        }

        Map<Pair<Integer, Integer>, List<Pair<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>>> commonPath = rewrites.stream().collect(Collectors.groupingBy(rw -> rw.getLeft().head()));

        List<Term> contents;
        if (subject instanceof KItem) {
            contents = ((KList) ((KItem) subject).kList()).getContents();
        } else if (subject instanceof BuiltinList) {
            contents = ((BuiltinList) subject).children;
        } else {
            throw new AssertionError("unexpected rewrite in subject: " + subject);
        }
        List<Term> newContents = new ArrayList<>();

        for (int i = 0; i < contents.size(); i++) {
            Pair<Integer, Integer> pair = Pair.of(i, i + 1);
            if (commonPath.containsKey(pair)) {
                List<Pair<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>> theInnerRewrites = commonPath.get(pair).stream().map(p -> Pair.of(
                        (scala.collection.immutable.List<Pair<Integer, Integer>>) p.getLeft().tail(), p.getRight())).collect(Collectors.toList());
                newContents.add(buildRHS(contents.get(i), substitution, theInnerRewrites, context));
            } else {
                newContents.add(contents.get(i));
            }
        }

        if (subject instanceof KItem) {
            return KItem.of(((KItem) subject).kLabel(), KList.concatenate(newContents), context.global()).applyAnywhereRules(false, context);
        } else if (subject instanceof BuiltinList) {
            return BuiltinList
                    .builder(((BuiltinList) subject).sort, ((BuiltinList) subject).operatorKLabel, ((BuiltinList) subject).unitKLabel, ((BuiltinList) subject).globalContext())
                    .addAll(newContents)
                    .build();
        } else {
            throw new AssertionError("unexpected rewrite in subject: " + subject);
        }
    }

    private List<ConstrainedTerm> computeRewriteStepByRule(ConstrainedTerm subject, Rule rule) {
        List<ConstrainedTerm> results = Collections.emptyList();
        try {
            if (rule == RuleAuditing.getAuditingRule()) {
                RuleAuditing.beginAudit();
            } else if (RuleAuditing.isAuditBegun() && RuleAuditing.getAuditingRule() == null) {
                System.err.println("\nAuditing " + rule + "...\n");
            }

            return results = subject.unify(rule.createLhsPattern(subject.termContext()),
                    rule.matchingInstructions(), rule.lhsOfReadCell(), rule.matchingVariables())
                    .stream()
                    .map(s -> buildResult(rule, s.getLeft(), subject.term(), !s.getRight(), subject.termContext()))
                    .collect(Collectors.toList());
        } catch (KEMException e) {
            e.exception.addTraceFrame("while evaluating rule at " + rule.getSource() + rule.getLocation());
            throw e;
        } finally {
            if (!results.isEmpty()) {
                RuleAuditing.succeed(rule);
                Coverage.print(subject.termContext().global().krunOptions.experimental.coverage, subject);
                Coverage.print(subject.termContext().global().krunOptions.experimental.coverage, rule);
            }

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

    /**
     * Builds the result of rewrite based on the unification constraint.
     * It applies the unification constraint on the right-hand side of the rewrite rule,
     * if the rule is not compiled for fast rewriting.
     * It uses build instructions, if the rule is compiled for fast rewriting.
     */
    public static ConstrainedTerm buildResult(
            Rule rule,
            ConjunctiveFormula constraint,
            Term subject,
            boolean expandPattern,
            TermContext context) {
        for (Variable variable : rule.freshConstants()) {
            constraint = constraint.add(
                    variable,
                    FreshOperations.freshOfSort(variable.sort(), context));
        }
        constraint = constraint.addAll(rule.ensures()).simplify(context);

        Term term;

        /* apply the constraints substitution on the rule RHS */
        context.setTopConstraint(constraint);
        Set<Variable> substitutedVars = Sets.union(rule.freshConstants(), rule.matchingVariables());
        constraint = constraint.orientSubstitution(substitutedVars);
        if (rule.isCompiledForFastRewriting()) {
            term = AbstractKMachine.apply((CellCollection) subject, constraint.substitution(), rule, context);
        } else {
            term = rule.rightHandSide().substituteAndEvaluate(constraint.substitution(), context);
        }

        /* eliminate bindings of the substituted variables */
        constraint = constraint.removeBindings(substitutedVars);

        /* get fresh substitutions of rule variables */
        Map<Variable, Variable> renameSubst = Variable.rename(rule.variableSet());

        /* rename rule variables in both the term and the constraint */
        term = term.substituteWithBinders(renameSubst);
        constraint = ((ConjunctiveFormula) constraint.substituteWithBinders(renameSubst)).simplify(context);

        ConstrainedTerm result = new ConstrainedTerm(term, constraint, context);
        if (expandPattern) {
            if (rule.isCompiledForFastRewriting()) {
                result = new ConstrainedTerm(term.substituteAndEvaluate(constraint.substitution(), context), constraint, context);
            }
            // TODO(AndreiS): move these some other place
            result = result.expandPatterns(true);
            if (result.constraint().isFalse() || result.constraint().checkUnsat()) {
                result = null;
            }
        }

        return result;
    }

    /**
     * Unifies the term with the pattern, and computes a map from variables in
     * the pattern to the terms they unify with. Adds as many search results
     * up to the bound as were found, and returns {@code true} if the bound has been reached.
     */
    private boolean addSearchResult(
            HashSet<Substitution<Variable, Term>> searchResults,
            ConstrainedTerm subject,
            Rule pattern,
            int bound) {
        assert Sets.intersection(subject.term().variableSet(),
                subject.constraint().substitution().keySet()).isEmpty();
        assert pattern.requires().stream().allMatch(BoolToken.TRUE::equals) && pattern.lookups().getKComponents().isEmpty();
        List<Substitution<Variable, Term>> discoveredSearchResults = FastRuleMatcher.match(
                subject.term(),
                pattern.leftHandSide(),
                subject.termContext());
        for (Substitution<Variable, Term> searchResult : discoveredSearchResults) {
            searchResults.add(searchResult);
            if (searchResults.size() == bound) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param initialTerm
     * @param pattern     the pattern we are searching for
     * @param bound       a negative value specifies no bound
     * @param depth       a negative value specifies no bound
     * @param searchType  defines when we will attempt to match the pattern
     * @return a list of substitution mappings for results that matched the pattern
     */
    public Set<Substitution<Variable, Term>> search(
            Term initialTerm,
            Rule pattern,
            int bound,
            int depth,
            SearchType searchType,
            TermContext context) {
        stopwatch.start();

        HashSet<Substitution<Variable, Term>> searchResults = Sets.newHashSet();
        Set<ConstrainedTerm> visited = Sets.newHashSet();

        ConstrainedTerm initCnstrTerm = new ConstrainedTerm(initialTerm, context);

        // If depth is 0 then we are just trying to match the pattern.
        // A more clean solution would require a bit of a rework to how patterns
        // are handled in krun.Main when not doing search.
        if (depth == 0) {
            addSearchResult(searchResults, initCnstrTerm, pattern, bound);
            stopwatch.stop();
            if (context.global().krunOptions.experimental.statistics)
                System.err.println("[" + visited.size() + "states, " + 0 + "steps, " + stopwatch + "]");
            return searchResults;
        }

        // The search queues will map terms to their depth in terms of transitions.
        Map<ConstrainedTerm, Integer> queue = Maps.newLinkedHashMap();
        Map<ConstrainedTerm, Integer> nextQueue = Maps.newLinkedHashMap();

        visited.add(initCnstrTerm);
        queue.put(initCnstrTerm, 0);

        if (searchType == SearchType.ONE) {
            depth = 1;
        }
        if (searchType == SearchType.STAR) {
            if (addSearchResult(searchResults, initCnstrTerm, pattern, bound)) {
                stopwatch.stop();
                if (context.global().krunOptions.experimental.statistics)
                    System.err.println("[" + visited.size() + "states, " + 0 + "steps, " + stopwatch + "]");
                return searchResults;
            }
        }

        int step;
    label:
        for (step = 0; !queue.isEmpty(); ++step) {
            superheated.clear();
            superheated.addAll(newSuperheated);
            newSuperheated.clear();
            for (Map.Entry<ConstrainedTerm, Integer> entry : queue.entrySet()) {
                ConstrainedTerm term = entry.getKey();
                Integer currentDepth = entry.getValue();

                List<ConstrainedTerm> results = computeRewriteStep(term, step, false);

                if (results.isEmpty() && searchType == SearchType.FINAL) {
                    if (addSearchResult(searchResults, term, pattern, bound)) {
                        break label;
                    }
                }

                for (ConstrainedTerm result : results) {
                    if (!transition) {
                        nextQueue.put(result, currentDepth);
                        break;
                    } else {
                        // Continue searching if we haven't reached our target
                        // depth and we haven't already visited this state.
                        if (currentDepth + 1 != depth && visited.add(result)) {
                            nextQueue.put(result, currentDepth + 1);
                        }
                        // If we aren't searching for only final results, then
                        // also add this as a result if it matches the pattern.
                        if (searchType != SearchType.FINAL || currentDepth + 1 == depth) {
                            if (addSearchResult(searchResults, result, pattern, bound)) {
                                break label;
                            }
                        }
                    }
                }
            }

            /* swap the queues */
            Map<ConstrainedTerm, Integer> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        stopwatch.stop();
        if (context.global().krunOptions.experimental.statistics) {
            System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");
        }

        Set<Substitution<Variable, Term>> adaptedResults = searchResults.stream().map(r -> {
            RenameAnonymousVariables renameAnonymousVariables = new RenameAnonymousVariables();
            Substitution<Variable, Term> subs = new HashMapSubstitution();
            r.forEach((k, v) -> subs.plus(renameAnonymousVariables.getRenamedVariable(k), renameAnonymousVariables.apply(v)));
            return subs;
        }).collect(Collectors.toSet());

        return adaptedResults;
    }

    public List<ConstrainedTerm> proveRule(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> specRules) {
        List<ConstrainedTerm> proofResults = new ArrayList<>();
        Set<ConstrainedTerm> visited = new HashSet<>();
        List<ConstrainedTerm> queue = new ArrayList<>();
        List<ConstrainedTerm> nextQueue = new ArrayList<>();

        initialTerm = initialTerm.expandPatterns(true);

        visited.add(initialTerm);
        queue.add(initialTerm);
        boolean guarded = false;
        int step = 0;
        while (!queue.isEmpty()) {
            step++;
            for (ConstrainedTerm term : queue) {
                if (term.implies(targetTerm)) {
                    continue;
                }

                List<Term> leftKContents = term.term().getCellContentsByName(CellLabel.K);
                List<Term> rightKContents = targetTerm.term().getCellContentsByName(CellLabel.K);
                // TODO(YilongL): the `get(0)` seems hacky
                if (leftKContents.size() == 1 && rightKContents.size() == 1) {
                    Pair<Term, Variable> leftKPattern = KSequence.splitContentAndFrame(leftKContents.get(0));
                    Pair<Term, Variable> rightKPattern = KSequence.splitContentAndFrame(rightKContents.get(0));
                    if (leftKPattern.getRight() != null && rightKPattern.getRight() != null
                            && leftKPattern.getRight().equals(rightKPattern.getRight())) {
                        BoolToken matchable = MetaK.matchable(
                                leftKPattern.getLeft(),
                                rightKPattern.getLeft(),
                                term.termContext());
                        if (matchable != null && matchable.booleanValue()) {
                            proofResults.add(term);
                            continue;
                        }
                    }
                }

                if (guarded) {
                    ConstrainedTerm result = applySpecRules(term, specRules);
                    if (result != null) {
                        if (visited.add(result))
                            nextQueue.add(result);
                        continue;
                    }
                }

                List<ConstrainedTerm> results = slowComputeRewriteStep(term, step, false);
                if (results.isEmpty()) {
                    /* final term */
                    proofResults.add(term);
                } else {
//                    for (Rule rule : appliedRules) {
//                        System.err.println(rule.getLocation() + " " + rule.getSource());
//                    }

                    /* add helper rule */
                    HashSet<Variable> ruleVariables = new HashSet<>(initialTerm.variableSet());
                    ruleVariables.addAll(targetTerm.variableSet());

                    /*
                    rules.add(new Rule(
                            term.term().substitute(freshSubstitution, definition),
                            targetTerm.term().substitute(freshSubstitution, definition),
                            term.constraint().substitute(freshSubstitution, definition),
                            Collections.<Variable>emptyList(),
                            new SymbolicConstraint(definition).substitute(freshSubstitution, definition),
                            IndexingPair.getIndexingPair(term.term()),
                            new Attributes()));
                     */
                }

                for (ConstrainedTerm cterm : results) {
                    ConstrainedTerm result = new ConstrainedTerm(
                            cterm.term(),
                            cterm.constraint().removeBindings(
                                    Sets.difference(
                                            cterm.constraint().substitution().keySet(),
                                            initialTerm.variableSet())),
                            cterm.termContext());
                    if (visited.add(result)) {
                        nextQueue.add(result);
                    }
                }
            }

            /* swap the queues */
            List<ConstrainedTerm> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
            guarded = true;
        }

        return proofResults;
    }

    /**
     * Applies the first applicable specification rule and returns the result.
     */
    private ConstrainedTerm applySpecRules(ConstrainedTerm constrainedTerm, List<Rule> specRules) {
        for (Rule specRule : specRules) {
            ConstrainedTerm pattern = specRule.createLhsPattern(constrainedTerm.termContext());
            ConjunctiveFormula constraint = constrainedTerm.matchImplies(pattern, true);
            if (constraint != null) {
                return buildResult(specRule, constraint, null, true, constrainedTerm.termContext());
            }
        }
        return null;
    }

}

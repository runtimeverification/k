// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.base.Stopwatch;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.RewriterResult;
import org.kframework.Strategy;
import org.kframework.attributes.Att;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.StateLog;
import org.kframework.builtin.KLabels;
import org.kframework.kore.FindK;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KORE;
import org.kframework.kprove.KProve;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Main;
import org.kframework.rewriter.SearchType;
import org.kframework.backend.java.utils.BitSet;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.io.File;

/**
 * @author AndreiS
 */
public class SymbolicRewriter {

    private final List<String> transitions;
    private final Stopwatch stopwatch = Stopwatch.createUnstarted();
    private final KOREtoBackendKIL constructor;
    private final GlobalOptions globalOptions;
    private final GlobalContext global;
    private boolean transition;
    private final Set<ConstrainedTerm> superheated = Sets.newHashSet();
    private final Set<ConstrainedTerm> newSuperheated = Sets.newHashSet();
    private final FastRuleMatcher theFastMatcher;
    private final Definition definition;
    private final BitSet allRuleBits;

    public SymbolicRewriter(GlobalContext global, List<String> transitions,
                            KOREtoBackendKIL constructor) {
        this.constructor = constructor;
        this.definition = global.getDefinition();
        this.allRuleBits = BitSet.apply(definition.ruleTable.size());
        this.allRuleBits.makeOnes(definition.ruleTable.size());
        this.transitions = transitions;
        this.theFastMatcher = new FastRuleMatcher(global, definition.ruleTable.size());
        this.transition = true;
        this.global = global;
        this.globalOptions = global.globalOptions;
    }

    public KOREtoBackendKIL getConstructor() {
        return constructor;
    }

    public RewriterResult rewrite(ConstrainedTerm constrainedTerm, int bound) {
        stopwatch.start();
        int step = 0;
        List<ConstrainedTerm> results;
        while (step != bound && !(results = computeRewriteStep(constrainedTerm, step, true)).isEmpty()) {
            /* get the first solution */
            constrainedTerm = results.get(0);
            step++;
        }

        ConstrainedTerm afterVariableRename = new ConstrainedTerm(constrainedTerm.term(), constrainedTerm.termContext());

        stopwatch.stop();
        return new RewriterResult(Optional.of(step), Optional.empty(), afterVariableRename.term());
    }

    private List<ConstrainedTerm> computeRewriteStep(ConstrainedTerm constrainedTerm, int step, boolean computeOne) {
        return fastComputeRewriteStep(constrainedTerm, computeOne, false, false, step);
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

        if ((topOfStrategyCell instanceof KApply) && KLabels.KSEQ.equals(((KApply) topOfStrategyCell).klabel())) {
            topOfStrategyCell = ((KApply) topOfStrategyCell).klist().items().get(0);
        }
        boolean isStuck = !(topOfStrategyCell instanceof KApply) ||
                ((KApply) topOfStrategyCell).klabel().name().equals(Att.stuck());


        // if we are stuck (i.e., in this method) and the #STUCK marker is the top of the strategy cell, do nothing
        if (isStuck) {
            return Optional.empty();
        }

        // otherwise, add the #STUCK label to the top of the strategy cell

        Att emptyAtt = Att.empty();

        K stuck = constructor.KApply1(constructor.KLabel(Att.stuck()), constructor.KList(Collections.emptyList()), emptyAtt);
        List<K> items = new LinkedList<>(((KApply) theStrategy.get()).klist().items());
        items.add(0, stuck);
        K sContent = constructor.KApply1(constructor.KLabel(KLabels.KSEQ), constructor.KList(items), emptyAtt);
        K s = constructor.KApply1(((KApply) theStrategy.get()).klabel(), constructor.KList(Collections.singletonList(sContent)), emptyAtt);
        Term entireConf = constructor.KApply1(((KApply) subject.term()).klabel(),
                constructor.KList(((KApply) subject.term()).klist().stream().map(k ->
                        k instanceof KApply && ((KApply) k).klabel().name().contains(Strategy.strategyCellName()) ? s : k).collect(Collectors.toList())), emptyAtt);
        return Optional.of(new ConstrainedTerm(entireConf, subject.termContext()));

    }

    public List<ConstrainedTerm> fastComputeRewriteStep(ConstrainedTerm subject, boolean computeOne, boolean narrowing, boolean proofFlag, int step) {
        global.stateLog.log(StateLog.LogEvent.NODE, subject.term(), subject.constraint());
        List<ConstrainedTerm> results = new ArrayList<>();
        if (definition.automaton == null) {
            return results;
        }
        List<FastRuleMatcher.RuleMatchResult> matches = theFastMatcher.matchRulePattern(
                subject,
                definition.automaton.leftHandSide(),
                allRuleBits,
                narrowing,
                computeOne,
                transitions,
                proofFlag,
                subject.termContext(), step);
        for (FastRuleMatcher.RuleMatchResult matchResult : matches) {
            Rule rule = definition.ruleTable.get(matchResult.ruleIndex);
            global.stateLog.log(StateLog.LogEvent.RULEATTEMPT, rule.toKRewrite());
            if (globalOptions.logRulesPublic) {
                System.err.println("\n" + rule);
            }

            Substitution<Variable, Term> substitution =
                    rule.att().contains(Att.refers_THIS_CONFIGURATION()) ?
                            matchResult.constraint.substitution().plus(new Variable(KLabels.THIS_CONFIGURATION, Sort.KSEQUENCE), filterOurStrategyCell(subject.term())) :
                            matchResult.constraint.substitution();
            // start the optimized substitution

            // get a map from AST paths to (fine-grained, inner) rewrite RHSs
            assert (matchResult.rewrites.size() > 0);
            Term theNew;
            if (matchResult.rewrites.size() == 1)
            // use the more efficient implementation if we only have one rewrite
            {
                theNew = buildRHS(subject.term(), substitution, matchResult.rewrites.keySet().iterator().next(),
                        matchResult.rewrites.values().iterator().next(), subject.termContext());
            } else {
                theNew = buildRHS(subject.term(), substitution,
                        matchResult.rewrites.entrySet().stream().map(e -> Pair.of(e.getKey(), e.getValue())).collect(Collectors.toList()),
                        subject.termContext());
            }

            if (!matchResult.isMatching) {
                theNew = theNew.substituteAndEvaluate(substitution, subject.termContext());
            }

            theNew = restoreConfigurationIfNecessary(subject, rule, theNew);

            /* eliminate bindings of the substituted variables */
            ConjunctiveFormula constraint = matchResult.constraint;
            constraint = constraint.removeBindings(rule.variableSet());

            /* get fresh substitutions of rule variables */
            Map<Variable, Variable> renameSubst = Variable.rename(rule.variableSet());

            /* rename rule variables in both the term and the constraint */
            theNew = theNew.substituteWithBinders(renameSubst);
            constraint = ((ConjunctiveFormula) constraint.substituteWithBinders(renameSubst)).simplify(subject.termContext());

            ConstrainedTerm result = new ConstrainedTerm(theNew, constraint, subject.termContext());
            if (!matchResult.isMatching) {
                // TODO(AndreiS): move these some other place
                result = result.expandPatterns(true);
                if (result.constraint().isFalseExtended() || result.constraint().checkUnsat()) {
                    if (globalOptions.logRulesPublic) {
                        System.err.println("Execution path aborted");
                    }
                    continue;
                }
            }

            /* TODO(AndreiS): remove this hack for super strictness after strategies work */
            if (rule.att().contains(Att.heat()) && transitions.stream().anyMatch(rule.att()::contains)) {
                newSuperheated.add(result);
            } else if (rule.att().contains(Att.cool()) && transitions.stream().anyMatch(rule.att()::contains) && superheated.contains(subject)) {
                if (globalOptions.logRulesPublic) {
                    System.err.println("Execution path aborted");
                }
                continue;
            }

            global.stateLog.log(StateLog.LogEvent.RULE, rule.toKRewrite());
            results.add(result);
        }

        if (results.isEmpty()) {
            addStuckFlagIfNotThere(subject).ifPresent(results::add);
        }

        return results;
    }

    private Term restoreConfigurationIfNecessary(ConstrainedTerm subject, Rule rule, Term theNew) {
        if (rule.att().contains(Att.refers_RESTORE_CONFIGURATION())) {
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

            strategyCell = ((Term) strategyCell).accept(new CopyOnWriteTransformer() {
                @Override
                public JavaSymbolicObject transform(KItem kItem) {
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
            public JavaSymbolicObject transform(KItem kItem) {

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
                //noinspection RedundantCast
                newContents.set(path.head().getLeft(), buildRHS(newContents.get(path.head().getLeft()), substitution,
                        (scala.collection.immutable.List<Pair<Integer, Integer>>) path.tail(), rhs, context));
                return KItem.of(kItemSubject.kLabel(), KList.concatenate(newContents), context.global()).applyAnywhereRules(context);
            } else if (subject instanceof BuiltinList) {
                BuiltinList builtinListSubject = (BuiltinList) subject;
                List<Term> newContents = new ArrayList<>(builtinListSubject.children);
                //noinspection RedundantCast
                newContents.set(path.head().getLeft(), buildRHS(newContents.get(path.head().getLeft()), substitution,
                        (scala.collection.immutable.List<Pair<Integer, Integer>>) path.tail(), rhs, context));
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
                //noinspection RedundantCast
                List<Pair<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>> theInnerRewrites = commonPath.get(pair).stream().map(p -> Pair.of(
                        (scala.collection.immutable.List<Pair<Integer, Integer>>) p.getLeft().tail(), p.getRight())).collect(Collectors.toList());
                newContents.add(buildRHS(contents.get(i), substitution, theInnerRewrites, context));
            } else {
                newContents.add(contents.get(i));
            }
        }

        if (subject instanceof KItem) {
            return KItem.of(((KItem) subject).kLabel(), KList.concatenate(newContents), context.global()).applyAnywhereRules(context);
        } else
            //noinspection ConstantConditions
            if (subject instanceof BuiltinList) {
            return BuiltinList
                    .builder(((BuiltinList) subject).sort, ((BuiltinList) subject).operatorKLabel, ((BuiltinList) subject).unitKLabel, ((BuiltinList) subject).globalContext())
                    .addAll(newContents)
                    .build();
        } else {
            throw new AssertionError("unexpected rewrite in subject: " + subject);
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
            @SuppressWarnings("unused") Term subject,
            boolean expandPattern,
            TermContext context) {
        for (Variable variable : rule.freshConstants()) {
            constraint = constraint.add(
                    variable,
                    FreshOperations.freshOfSort(variable.sort(), context));
        }
        constraint = constraint.addAll(rule.ensures()).simplify(context);


        /* apply the constraints substitution on the rule RHS */
        Set<Variable> substitutedVars = Sets.union(rule.freshConstants(), rule.matchingVariables());
        constraint = constraint.orientSubstitution(substitutedVars);
        context.setTopConstraint(constraint);
        Term term = rule.rightHandSide().substituteAndEvaluate(constraint.substitution(), context);

        /* eliminate bindings of the substituted variables */
        constraint = constraint.removeBindings(substitutedVars);

        /* get fresh substitutions of rule variables */
        Map<Variable, Variable> renameSubst = Variable.rename(rule.variableSet());

        /* rename rule variables in both the term and the constraint */
        term = term.substituteWithBinders(renameSubst);
        constraint = ((ConjunctiveFormula) constraint.substituteWithBinders(renameSubst)).simplify(context);

        ConstrainedTerm result = new ConstrainedTerm(term, constraint, context);
        if (expandPattern) {
            // TODO(AndreiS): move these some other place
            result = result.expandPatterns(true);
            if (result.constraint().isFalseExtended() || result.constraint().checkUnsat()) {
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
            List<K> searchResults,
            ConstrainedTerm subject,
            Rule pattern,
            int bound,
            TermContext context) {
        //noinspection AssertWithSideEffects
        assert Sets.intersection(subject.term().variableSet(),
                subject.constraint().substitution().keySet()).isEmpty();
        assert pattern.requires().stream().allMatch(BoolToken.TRUE::equals) && pattern.lookups().getKComponents().isEmpty();
        List<Substitution<Variable, Term>> discoveredSearchResults = FastRuleMatcher.match(
                subject.term(),
                pattern.leftHandSide(),
                subject.termContext());
        if (!discoveredSearchResults.isEmpty()) {
            for (Substitution<Variable, Term> searchResult : discoveredSearchResults) {
                ConjunctiveFormula conjunct = new ConjunctiveFormula(searchResult, subject.constraint().equalities(), PersistentUniqueList.empty(), subject.constraint().truthValue(), context.global());
                searchResults.add(conjunct);
            }
        }
        return searchResults.size() == bound;
    }

    /**
     * @param initialTerm
     * @param pattern     the pattern we are searching for
     * @param bound       a negative javaBackendValue specifies no bound
     * @param depth       a negative javaBackendValue specifies no bound
     * @param searchType  defines when we will attempt to match the pattern
     * @return a list of substitution mappings for results that matched the pattern
     */

    public K search(
            Term initialTerm,
            Rule pattern,
            int bound,
            int depth,
            SearchType searchType,
            TermContext context) {
        stopwatch.start();

        List<K> searchResults = new ArrayList<>();
        Set<ConstrainedTerm> visited = Sets.newHashSet();

        ConstrainedTerm initCnstrTerm = new ConstrainedTerm(initialTerm, context);

        // If depth is 0 then we are just trying to match the pattern.
        // A more clean solution would require a bit of a rework to how patterns
        // are handled in krun.Main when not doing search.
        if (depth == 0) {
            addSearchResult(searchResults, initCnstrTerm, pattern, bound, context);
            stopwatch.stop();
            if (context.global().krunOptions.experimental.statistics)
                System.err.println("[" + visited.size() + "states, " + 0 + "steps, " + stopwatch + "]");
            return disjunctResults(searchResults);
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
            if (addSearchResult(searchResults, initCnstrTerm, pattern, bound, context)) {
                stopwatch.stop();
                if (context.global().krunOptions.experimental.statistics)
                    System.err.println("[" + visited.size() + "states, " + 0 + "steps, " + stopwatch + "]");
                return disjunctResults(searchResults);
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
                    if (addSearchResult(searchResults, term, pattern, bound, context)) {
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
                            if (addSearchResult(searchResults, result, pattern, bound, context)) {
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
        return disjunctResults(searchResults);
    }

    private K kApplyConversion(K k) {
        if (k instanceof KItem) {
            KItem kItem = (KItem) k;
            return KORE.KApply(kItem.klabel(), kItem.klist());
        }
        return k;
    }

    private Substitution<Variable, Term> filterSubstitution(Substitution<Variable, Term> subst) {
        Set<Variable> anonKeys = subst.keySet().stream().filter(v -> v.att().contains("anonymous")).collect(Collectors.toSet());
        return subst.minusAll(anonKeys);
    }

    private K processConjuncts(ConjunctiveFormula conjunct) {
        conjunct = new ConjunctiveFormula(
            filterSubstitution(conjunct.substitution()),
            conjunct.equalities(),
            conjunct.disjunctions(),
            conjunct.truthValue(),
            conjunct.globalContext());
        return kApplyConversion(conjunct.toKore());
    }

    private K disjunctResults(List<K> results) {
        return results.stream().map(x -> x instanceof ConjunctiveFormula ? processConjuncts((ConjunctiveFormula) x) : x)
                .distinct()
                .reduce((x, y) -> KORE.KApply(KLabels.ML_OR, x, y)).orElse(KORE.KApply(KLabels.ML_FALSE));
    }

    public List<ConstrainedTerm> proveRule(
            Rule rule, ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> specRules, KExceptionManager kem) {
        List<ConstrainedTerm> proofResults = new ArrayList<>();
        int successPaths = 0;
        Set<ConstrainedTerm> visited = new HashSet<>();
        List<ConstrainedTerm> queue = new ArrayList<>();
        List<ConstrainedTerm> nextQueue = new ArrayList<>();

        initialTerm = initialTerm.expandPatterns(true);

        global.stateLog.log(StateLog.LogEvent.REACHINIT,   initialTerm.term(), initialTerm.constraint());
        global.stateLog.log(StateLog.LogEvent.REACHTARGET, targetTerm.term(),  targetTerm.constraint());

        visited.add(initialTerm);
        queue.add(initialTerm);
        boolean guarded = false;
        int step = 0;
        globalOptions.logRulesPublic = globalOptions.logRules;
        globalOptions.logBasic |= globalOptions.logStmtsOnly | globalOptions.log;

        if (globalOptions.log) {
            System.out.println("\nTarget term\n=====================\n");
            System.out.println(targetTerm);
        }
        String targetCallDataStr;
        try {
            targetCallDataStr = ((KList) ((KItem) ((KList) ((KItem) ((KList) ((KItem) ((KList) ((KItem) targetTerm.term()).kList())
                    .get(5)).kList()).get(0)).klist()).get(5)).klist()).get(4).toString();
        } catch (Exception e) {
            System.err.println("Specification rule does not match expected spec form: " + targetTerm);
            throw e;
        }
        int branchingRemaining = globalOptions.branchingAllowed;
        boolean nextStepLogEnabled = false;
        while (!queue.isEmpty()) {
            step++;
            int v = 0;
            boolean oldLogEnabled = globalOptions.log;
            if (nextStepLogEnabled) {
                globalOptions.log = true;
            }
            nextStepLogEnabled = false;

            for (ConstrainedTerm term : queue) {
                v++;
                Term generatedTop = term.term();
                Term k = ((KList) ((KItem) generatedTop).kList()).get(0);
                Term kContent = ((KList) ((KItem) k).klist()).get(0);
                BuiltinList kSequence = kContent instanceof BuiltinList ? (BuiltinList) kContent : null;
                boolean isHalt = kSequence != null
                        ? kSequence.size() == 2 && kSequence.get(0) instanceof KItem
                        && kSequence.get(0).toString().equals("#halt_EVM(.KList)")
                        && !kSequence.get(1).toString().equals("#execute_EVM(.KList)")
                        : kContent.toString().equals("#halt_EVM(.KList)");
                boolean oldDebug =  globalOptions.debug;
                boolean oldLog = globalOptions.log;

                if (isHalt && globalOptions.debugLastStep
                        || globalOptions.debugSteps.contains(String.valueOf(step))) {
                    globalOptions.debug = true;
                    globalOptions.log = true;
                }
                if (term.implies(targetTerm)) {
                    global.stateLog.log(StateLog.LogEvent.REACHPROVED, term.term(), term.constraint());
                    successPaths++;
                    if (globalOptions.logBasic) {
                        System.out.println("\n============\nStep " + step + ": eliminated!\n============\n");
                        logStep(step, v, targetCallDataStr, term, true);
                    }
                    continue;
                } else {
                    logStep(step, v, targetCallDataStr, term, step == 1 && globalOptions.logBasic);
                }

                //stopping at halt
                if (isHalt) {
                    if (!globalOptions.log) {
                        logStep(step, v, targetCallDataStr, term, globalOptions.logBasic);
                    }
                    System.out.println("Halt! Terminating branch.");
                    proofResults.add(term);
                    continue;
                }


                /* TODO(AndreiS): terminate the proof with failure based on the klabel _~>_
                List<Term> leftKContents = term.term().getCellContentsByName("<k>");
                List<Term> rightKContents = targetTerm.term().getCellContentsByName("<k>");
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
                }*/

                if (guarded) {
                    ConstrainedTerm result = applySpecRules(term, specRules);
                    if (result != null) {
                        nextStepLogEnabled = true;
                        if (!globalOptions.log) {
                            logStep(step, v, targetCallDataStr, term, true);
                        }
                        // re-running constraint generation again for debug purposes
                        if (globalOptions.logBasic) {
                            System.err.println("\nApplying specification rule\n=========================\n");
                        }
                        if (globalOptions.debugSpecRules && !globalOptions.debug) {
                            boolean oldDebug2 = globalOptions.debug;
                            globalOptions.debug = true;
                            applySpecRules(term, specRules);
                            globalOptions.debug = oldDebug2;
                        }
                        if (visited.add(result)) {
                            nextQueue.add(result);
                        } else {
                            if (term.equals(result)) {
                                kem.registerCriticalWarning("Step " + step + ": infinite loop after applying a spec rule.");
                            }
                        }
                        continue;
                    }
                }

                List<ConstrainedTerm> results;
                try {
                    results = fastComputeRewriteStep(term, false, true, true, step);
                } catch (Throwable e) {
                    if (!globalOptions.log) {
                        logStep(step, v, targetCallDataStr, term, true);
                    }
                    System.out.println("\n\nTerm throwing exception\n============================\n\n");
                    KProve.prettyPrint(term.term());
                    System.out.println("/\\");
                    KProve.prettyPrint(term.constraint());
                    e.printStackTrace();
                    throw e;
                }
                if (results.isEmpty()) {
                    if (!globalOptions.log) {
                        logStep(step, v, targetCallDataStr, term, true);
                    }
                    System.out.println("\nStep above: " + step + ", evaluation ended with no successors.");
                    /* final term */
                    proofResults.add(term);
                }

                if (results.size() > 1) {
                    nextStepLogEnabled = true;
                    if (!globalOptions.log) {
                        logStep(step, v, targetCallDataStr, term, true);
                    }
                    if (branchingRemaining == 0) {
                        System.out.println("\nHalt on branching!\n=====================\n");

                        proofResults.addAll(results);
                        continue;
                    } else {
                        branchingRemaining--;
                        if (globalOptions.logBasic) {
                            System.out.println("\nBranching!\n=====================\n");
                        }
                    }
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
                globalOptions.debug = oldDebug;
                globalOptions.log = oldLog;
            }

            /* swap the queues */
            List<ConstrainedTerm> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
            guarded = true;

            globalOptions.log = oldLogEnabled;
        }

        if (globalOptions.verbose) {
            printSummaryBox(rule, proofResults, successPaths, step);
        }
        //fixme rebase: check if not printed elsewhere
        for (ConstrainedTerm term : proofResults) {
            if (globalOptions.fast) {
                System.out.println(term);
            } else {
                KProve.prettyPrint(term.term());
            }
            System.out.println("/\\");
            KProve.prettyPrint(term.constraint());
            System.out.println();
        }
        return proofResults;
    }

    private void printSummaryBox(Rule rule, List<ConstrainedTerm> proofResults, int successPaths, int step) {
        if (proofResults.isEmpty()) {
            System.err.format("\nSPEC PROVED: %s %s\n==================================\nExecution paths: %d\n",
                    new File(rule.getSource().source()), rule.getLocation(), successPaths);
        } else {
            System.err.format("\nSPEC FAILED: %s %s\n==================================\n" +
                            "Success execution paths: %d\nFailed execution paths: %d\n",
                    new File(rule.getSource().source()), rule.getLocation(), successPaths, proofResults.size());
        }
        System.err.format("Longest path: %d steps\n", step);
        global.profiler.printResult();
    }

    private void logStep(int step, int v, String targetCallDataStr, ConstrainedTerm term, boolean forced) {
        if (!globalOptions.logBasic) {
            return;
        }
        Term generatedTop = term.term();
        Term k = ((KList) ((KItem) generatedTop).kList()).get(0);
        Term ethereum = ((KList) ((KItem) generatedTop).kList()).get(5);
        Term evm = ((KList) ((KItem) ethereum).klist()).get(0);
        Term output = ((KList) ((KItem) evm).kList()).get(0);
        Term statusCode = ((KList) ((KItem) evm).kList()).get(1);
        Term callState = ((KList) ((KItem) evm).kList()).get(5);
        Term callData = ((KList) ((KItem) callState).kList()).get(4);
        Term wordStack = ((KList) ((KItem) callState).kList()).get(6);
        Term localMem = ((KList) ((KItem) callState).kList()).get(7);
        K theMap = ((KItem) localMem).klist().items().get(0);
        Term pc = ((KList) ((KItem) callState).kList()).get(8);
        Term gas = ((KList) ((KItem) callState).kList()).get(9);

        Term network = ((KList) ((KItem) ethereum).klist()).get(1);
        BuiltinMap accounts = (BuiltinMap) ((KList) ((KItem) ((KList) ((KItem) network).kList())
                .get(1)).klist()).get(0);

        if (!(theMap instanceof BuiltinMap || theMap instanceof Variable)) {
            forced = true;
        }

        Term kContent = ((KList) ((KItem) k).klist()).get(0);
        BuiltinList kSequence = kContent instanceof BuiltinList ? (BuiltinList) kContent : null;
        boolean inNewStmt = globalOptions.logStmtsOnly && kSequence != null && inNewStmt(kSequence);

        if (globalOptions.log || forced || inNewStmt || globalOptions.logRulesPublic) {
            System.out.format("\nSTEP %d v%d : %f s \n===================\n",
                    step, v, (System.currentTimeMillis() - Main.startTime) / 1000.);
        }

        if (globalOptions.log || forced || inNewStmt) {
            KProve.prettyPrint(k);
            System.out.println(output);
            System.out.println(statusCode);
            System.out.println("<localMem>");

            if (theMap instanceof BuiltinMap) {
                /*List<Term> entries = ((BuiltinMap) theMap).getKComponents();
                for (int i = 0; i < entries.size(); i += 10) {
                    System.out.println("\t" + entries.get(i));
                    System.out.println("\t...");
                }*/
                System.out.println("...");
            } else {
                System.out.println("\tNon-map format:");
                System.out.print("\t");
                System.out.println(theMap);
            }
            System.out.println("</localMem>");

            System.out.println(pc);
            System.out.println(gas);
            System.out.println(wordStack);
            String callDataStr = callData.toString();
            if (!targetCallDataStr.equals(callDataStr)) {
                System.out.println(callDataStr.substring(0, Math.min(callDataStr.length(), 300)));
            }
            System.out.println("accounts: " + accounts.getEntries().size());
            for (Map.Entry<Term, Term> acct : accounts.getEntries().entrySet()) {
                Term acctID = acct.getKey();
                K storage = ((KItem) acct.getValue()).klist().items().get(3);
                System.out.println(acctID);
                System.out.println(storage);
            }
            System.out.println("/\\");
            KProve.prettyPrint(term.constraint());
        }
        if (!(theMap instanceof BuiltinMap || theMap instanceof Variable)) {
            throw new RuntimeException("<localMem> non-map format, aborting.");
        }
    }

    private boolean inNewStmt(BuiltinList kSequence) {
        return kSequence.size() >= 2 && !kSequence.get(0).toString().startsWith("#")
                && kSequence.get(1).toString().startsWith("#pc");
    }

    /**
     * Applies the first applicable specification rule and returns the result.
     */
    private ConstrainedTerm applySpecRules(ConstrainedTerm constrainedTerm, List<Rule> specRules) {
        for (Rule specRule : specRules) {
            ConstrainedTerm pattern = specRule.createLhsPattern(constrainedTerm.termContext());
            ConjunctiveFormula constraint = constrainedTerm.matchImplies(pattern, true, specRule.matchingSymbols());
            if (constraint != null) {
                ConstrainedTerm result = buildResult(specRule, constraint, null, true, constrainedTerm.termContext());
                global.stateLog.log(StateLog.LogEvent.SRULE, specRule.toKRewrite());
                if (globalOptions.logRulesPublic) {
                    System.err.println("\n" + specRule);
                }
                return result;
            }
        }
        return null;
    }

}

// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.base.Stopwatch;
import com.google.common.collect.ImmutableList;
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
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemRepresentation;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.FormulaContext;
import org.kframework.backend.java.util.RuleSourceUtil;
import org.kframework.backend.java.util.StateLog;
import org.kframework.backend.java.util.TimeMemoryEntry;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Rules;
import org.kframework.kore.FindK;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KORE;
import org.kframework.kprove.KProve;
import org.kframework.kprove.KProveOptions;
import org.kframework.rewriter.SearchType;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;

import javax.annotation.Nullable;
import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * @author AndreiS
 */
public class SymbolicRewriter {

    private final List<String> transitions;
    private final Stopwatch stopwatch = Stopwatch.createUnstarted();
    private final KOREtoBackendKIL constructor;
    private final GlobalContext global;
    private boolean transition;
    private final Set<ConstrainedTerm> superheated = Sets.newHashSet();
    private final Set<ConstrainedTerm> newSuperheated = Sets.newHashSet();
    private final FastRuleMatcher theFastMatcher;
    private final Definition definition;

    public SymbolicRewriter(GlobalContext global, List<String> transitions,
                            KOREtoBackendKIL constructor) {
        this.constructor = constructor;
        this.definition = global.getDefinition();
        this.transitions = transitions;
        this.theFastMatcher = new FastRuleMatcher(global);
        this.transition = true;
        this.global = global;
        parseLogCells();
    }

    public KOREtoBackendKIL getConstructor() {
        return constructor;
    }

    public RewriterResult rewrite(ConstrainedTerm constrainedTerm, int bound) {
        ConstrainedTerm initTerm = constrainedTerm;
        if (prettyInitTerm != null) {
            System.err.println("\nInitial term\n=====================\n");
            printTermAndConstraint(initTerm, prettyInitTerm, initTerm);
        }

        stopwatch.start();
        int step = 0;
        prevStats = new TimeMemoryEntry(false);

        List<ConstrainedTerm> results;
        while (step != bound && !(results = computeRewriteStep(constrainedTerm, step, true, initTerm)).isEmpty()) {
            /* get the first solution */
            constrainedTerm = results.get(0);

            step++;
            logStep(step, 1, constrainedTerm, false, false, initTerm);
        }

        ConstrainedTerm afterVariableRename = new ConstrainedTerm(constrainedTerm.term(), constrainedTerm.termContext());

        stopwatch.stop();
        if (global.globalOptions.verbose) {
            printSummaryBox(null, null, 1, step, 0);
        }
        return new RewriterResult(Optional.of(step), Optional.empty(), afterVariableRename.term());
    }

    private List<ConstrainedTerm> computeRewriteStep(ConstrainedTerm constrainedTerm, int step, boolean computeOne,
                                                     ConstrainedTerm initTerm) {
        return fastComputeRewriteStep(constrainedTerm, computeOne, false, false, step, initTerm);
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
                ((KApply) topOfStrategyCell).klabel().name().equals(KLabels.STUCK.name());


        // if we are stuck (i.e., in this method) and the #STUCK marker is the top of the strategy cell, do nothing
        if (isStuck) {
            return Optional.empty();
        }

        // otherwise, add the #STUCK label to the top of the strategy cell

        Att emptyAtt = Att.empty();

        K stuck = constructor.KApply1(KLabels.STUCK, constructor.KList(Collections.emptyList()), emptyAtt);
        List<K> items = new LinkedList<>(((KApply) theStrategy.get()).klist().items());
        items.add(0, stuck);
        K sContent = constructor.KApply1(constructor.KLabel(KLabels.KSEQ), constructor.KList(items), emptyAtt);
        K s = constructor.KApply1(((KApply) theStrategy.get()).klabel(), constructor.KList(Collections.singletonList(sContent)), emptyAtt);
        Term entireConf = constructor.KApply1(((KApply) subject.term()).klabel(),
                constructor.KList(((KApply) subject.term()).klist().stream().map(k ->
                        k instanceof KApply && ((KApply) k).klabel().name().contains(Strategy.strategyCellName()) ? s : k).collect(Collectors.toList())), emptyAtt);
        ConstrainedTerm stuckTerm = new ConstrainedTerm(entireConf, subject.constraint(), subject.termContext());
        global.stateLog.log(StateLog.LogEvent.RULE, Rules.STUCK_RULE, subject.term(), subject.constraint(), stuckTerm.term(), stuckTerm.constraint());
        return Optional.of(stuckTerm);
    }

    /**
     * @param proofFlag if true, ignore rules related to I/O.
     * @param step      for debugging only
     * @param initTerm  for logging only
     */
    public List<ConstrainedTerm> fastComputeRewriteStep(ConstrainedTerm subject, boolean computeOne, boolean narrowing,
                                                        boolean proofFlag, int step, ConstrainedTerm initTerm) {
        global.stateLog.log(StateLog.LogEvent.NODE, subject.term(), subject.constraint());
        List<ConstrainedTerm> results = new ArrayList<>();
        if (definition.mainAutomaton() == null) {
            //If there are no regular rules, do nothing.
            return results;
        }

        List<FastRuleMatcher.RuleMatchResult> matches = theFastMatcher.matchRulePattern(
                subject,
                narrowing,
                computeOne,
                transitions,
                proofFlag,
                subject.termContext(), step);
        if (global.javaExecutionOptions.logRulesPublic) {
            System.err.format("\nRegular rule processing matched phase, step %d\n" +
                    "==========================================\n", step);
        }
        for (FastRuleMatcher.RuleMatchResult matchResult : matches) {
            Rule rule = definition.ruleTable.get(matchResult.ruleIndex);
            global.stateLog.log(StateLog.LogEvent.RULEATTEMPT, rule.toKRewrite(), subject.term(), subject.constraint());
            if (global.javaExecutionOptions.logRulesPublic) {
                System.err.print("\nRegular rule: processing matched:\n-------------------------\n");
                RuleSourceUtil.printRuleAndSource(rule);
            }

            Substitution<Variable, Term> substitution =
                    rule.att().contains(Att.REFERS_THIS_CONFIGURATION()) ?
                            matchResult.constraint.substitution().plus(new Variable(KLabels.THIS_CONFIGURATION, Sort.KSEQUENCE), filterOurStrategyCell(subject.term())) :
                            matchResult.constraint.substitution();
            // start the optimized substitution

            if (global.javaExecutionOptions.logRulesPublic) {
                System.err.println("\nRegular rule: building match result\n-------------------------\n");
            }
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

            if (global.javaExecutionOptions.logRulesPublic) {
                System.err.println("\nRegular rule: evaluating rule application result\n-------------------------\n");
            }
            if (!matchResult.isMatching) {
                theNew = theNew.substituteAndEvaluate(substitution, subject.termContext());
            }

            theNew = restoreConfigurationIfNecessary(subject, rule, theNew);

            if (global.javaExecutionOptions.logRulesPublic) {
                System.err.println("\nRegular rule: evaluating constraint\n-------------------------\n");
            }
            /* eliminate bindings of the substituted variables */
            ConjunctiveFormula constraint = matchResult.constraint;
            constraint = constraint.removeSubstitutionVars(rule.variableSet());

            /* get fresh substitutions of rule variables */
            Map<Variable, Variable> renameSubst = Variable.rename(rule.variableSet());

            /* rename rule variables in both the term and the constraint */
            theNew = theNew.substituteWithBinders(renameSubst);
            constraint = ((ConjunctiveFormula) constraint.substituteWithBinders(renameSubst)).simplify(subject.termContext());

            ConstrainedTerm result = new ConstrainedTerm(theNew, constraint, subject.termContext());
            if (!matchResult.isMatching) {
                // TODO(AndreiS): move these some other place
                result = result.expandPatterns(true);
                if (result.constraint().isFalseExtended() || result.constraint().checkUnsat(
                        new FormulaContext(FormulaContext.Kind.RegularConstr, rule, global))) {
                    if (global.javaExecutionOptions.debugZ3) {
                        System.err.println("Execution path aborted after expanding patterns");
                    }
                    continue;
                }
            }

            /* TODO(AndreiS): remove this hack for super strictness after strategies work */
            if (rule.att().contains(Att.HEAT()) && transitions.stream().anyMatch(rule.att()::contains)) {
                newSuperheated.add(result);
            } else if (rule.att().contains(Att.COOL()) && transitions.stream().anyMatch(rule.att()::contains) && superheated.contains(subject)) {
                if (global.javaExecutionOptions.debugZ3) {
                    System.err.println("Execution path aborted, superheating logic");
                }
                continue;
            }

            global.stateLog.log(StateLog.LogEvent.RULE, rule.toKRewrite(), subject.term(), subject.constraint(), result.term(), result.constraint());
            if (global.javaExecutionOptions.debugZ3 && !result.constraint().equals(subject.constraint())) {
                System.err.format("New top constraint created: \n%s\n",
                        result.constraint().toStringDifferentiated(initTerm.constraint()));
            }
            results.add(result);
        }

        if (results.isEmpty()) {
            addStuckFlagIfNotThere(subject).ifPresent(results::add);
        }

        return results;
    }

    private Term restoreConfigurationIfNecessary(ConstrainedTerm subject, Rule rule, Term theNew) {
        if (rule.att().contains(Att.REFERS_RESTORE_CONFIGURATION())) {
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
                return KItem.of(kItemSubject.kLabel(), KList.concatenate(newContents), context.global())
                        .resolveFunctionAndAnywhere(context);
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
            return KItem.of(((KItem) subject).kLabel(), KList.concatenate(newContents), context.global())
                    .resolveFunctionAndAnywhere(context);
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
     *
     * @return {@code null} if result constraint is unsatisfiable.
     */
    public static ConstrainedTerm buildResult(
            Rule rule,
            ConjunctiveFormula constraint,
            @SuppressWarnings("unused") Term subject,
            boolean expandPattern,
            TermContext context, FormulaContext formulaContext) {
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
        constraint = constraint.removeSubstitutionVars(substitutedVars);

        /* get fresh substitutions of rule variables */
        Map<Variable, Variable> renameSubst = Variable.rename(rule.variableSet());

        /* rename rule variables in both the term and the constraint */
        term = term.substituteWithBinders(renameSubst);
        constraint = ((ConjunctiveFormula) constraint.substituteWithBinders(renameSubst)).simplify(context);
        constraint.globalContext().stateLog.log(StateLog.LogEvent.CHECKINGCONSTRAINT, constraint); // check if one comes here outside of specRule
        ConstrainedTerm result = new ConstrainedTerm(term, constraint, context);
        if (expandPattern) {
            // TODO(AndreiS): move these some other place
            result = result.expandPatterns(true);
            if (result.constraint().isFalseExtended() || result.constraint().checkUnsat(formulaContext)) {
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
            if (context.global().krunOptions.statistics)
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
                if (context.global().krunOptions.statistics)
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

                List<ConstrainedTerm> results = computeRewriteStep(term, step, false, initCnstrTerm);

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
        if (context.global().krunOptions.statistics) {
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
            KExceptionManager kem,
            @Nullable Rule boundaryPattern) {
        List<ConstrainedTerm> proofResults = new ArrayList<>();
        List<ConstrainedTerm> successResults = new ArrayList<>();
        int successPaths = 0;
        Set<ConstrainedTerm> visited = new HashSet<>();
        List<ConstrainedTerm> queue = new ArrayList<>();
        List<ConstrainedTerm> nextQueue = new ArrayList<>();

        List<Substitution<Variable, Term>> targetBoundarySub = null;
        if (boundaryPattern != null) {
            targetBoundarySub = getBoundarySubstitution(targetTerm, boundaryPattern);
            if (targetBoundarySub.isEmpty()) {
                throw KEMException.criticalError(
                        "Boundary pattern does not match the target term. Pattern: " + boundaryPattern.leftHandSide());
            }
        }

        visited.add(initialTerm);
        queue.add(initialTerm);
        int step = 0;

        if (prettyInitTerm != null) {
            System.err.println("\nInitial term\n=====================\n");
            printTermAndConstraint(initialTerm, prettyInitTerm, initialTerm);
        }
        if (prettyTarget != null) {
            System.err.println("\nTarget term\n=====================\n");
            printTermAndConstraint(targetTerm, prettyTarget, initialTerm);
        }
        int branchingRemaining = global.kproveOptions.branchingAllowed;
        boolean nextStepLogEnabled = false;
        boolean originalLog = global.javaExecutionOptions.log;
        prevStats = new TimeMemoryEntry(false);
        while (!queue.isEmpty()) {
            step++;
            int v = 0;
            global.javaExecutionOptions.log |= nextStepLogEnabled;
            nextStepLogEnabled = false;
            if (global.javaExecutionOptions.logProgress && step % 100 == 0) {
                System.err.print(".");
            }

            for (ConstrainedTerm term : queue) {
                boolean alreadyLogged = false;
                try {
                    v++;
                    term.termContext().setTopConstraint(null); //To remove leftover constraint from previous step
                    boolean boundaryCellsMatchTarget =
                            boundaryCellsMatchTarget(term, boundaryPattern, targetBoundarySub, step);
                    //var required to avoid logging the same step multiple times.
                    alreadyLogged = logStep(step, v, term,
                            step == 1 || boundaryCellsMatchTarget, false, initialTerm);
                    if (boundaryPattern == null || boundaryCellsMatchTarget) {
                        //Only test the full implication if there is no boundary pattern or if it is matched.
                        if (global.javaExecutionOptions.logRulesPublic) {
                            System.err.format("\nRegular rule final implication phase, step %d\n" +
                                    "==========================================\n", step);
                        }
                        if (term.implies(targetTerm, rule, !(boundaryPattern == null))) {
                            //If current term matches the target term, current execution path is proved.
                            global.stateLog.log(StateLog.LogEvent.REACHPROVED, term.term(), term.constraint());
                            if (global.javaExecutionOptions.logBasic) {
                                logStep(step, v, term, true, alreadyLogged, initialTerm);
                                System.err.println("\n============\nStep " + step + ": eliminated!\n============\n");
                            }
                            successPaths++;
                            successResults.add(term);
                            continue;
                        } else if (boundaryPattern != null && step > 1) {
                            //If boundary cells in current term match boundary cells in target term but entire terms
                            // don't match, halt execution.
                            logStep(step, v, term, global.javaExecutionOptions.logBasic, alreadyLogged, initialTerm);
                            System.err.println("Halt! Terminating branch.");
                            proofResults.add(term);
                            continue;
                        }
                        //else: case (no boundary pattern || (step == 1 && boundaryCellsMatchTarget))
                        //      && final implication == false
                        //  Do nothing. Boundary checking is disabled if there is no boundary pattern, or at step 1.
                        //  Disabling on step 1 is useful for specs that match 1 full loop iteration.
                    }

                    //Attempt to apply a spec rule, except on first step.
                    if (step > 1) {
                        ConstrainedTerm result = applySpecRules(term, step);
                        if (result != null) {
                            nextStepLogEnabled = true;
                            logStep(step, v, term, true, alreadyLogged, initialTerm);
                            // re-running constraint generation again for debug purposes
                            if (global.javaExecutionOptions.logBasic) {
                                System.err.println("\nApplying specification rule\n=========================\n");
                            }
                            if (visited.add(result)) {
                                nextQueue.add(result);
                            } else {
                                if (term.equals(result)) {
                                    throw KEMException.criticalError(
                                            "Step " + step + ": infinite loop after applying a spec rule.");
                                }
                            }
                            continue;
                        }
                    }

                    //Apply a regular rule
                    List<ConstrainedTerm> results = fastComputeRewriteStep(term, false, true, true, step,
                            initialTerm);
                    if (results.isEmpty()) {
                        logStep(step, v, term, true, alreadyLogged, initialTerm);
                        if (global.javaExecutionOptions.logBasic) {
                            System.err.println("\nStep above: " + step + ", evaluation ended with no successors.");
                        }
                        if (step == 1) {
                            kem.registerCriticalWarning(ExceptionType.PROOF_LINT, "Evaluation ended on 1st step. " +
                                    "Possible cause: non-functional term in constraint (path condition).");
                        }
                        /* final term */
                        proofResults.add(term);
                    }

                    if (results.size() > 1) {
                        nextStepLogEnabled = true;
                        logStep(step, v, term, true, alreadyLogged, initialTerm);
                        if (branchingRemaining == 0) {
                            System.err.println("\nHalt on branching!\n=====================\n");

                            proofResults.addAll(results);
                            continue;
                        } else {
                            branchingRemaining--;
                            if (global.javaExecutionOptions.logBasic) {
                                System.err.println("\nBranching!\n=====================\n");
                            }
                        }
                    }
                    //Build results of regular rule application
                    for (ConstrainedTerm cterm : results) {
                        ConstrainedTerm result = new ConstrainedTerm(
                                cterm.term(),
                                cterm.constraint().retainSubstitutionVars(initialTerm.variableSet()),
                                cterm.termContext());
                        if (visited.add(result)) {
                            nextQueue.add(result);
                        }
                    }

                    if (Thread.currentThread().isInterrupted()) {
                        throw KEMException.criticalError("Thread interrupted");
                    }
                } catch (OutOfMemoryError e) {
                    e.printStackTrace(); //to avoid hiding this exception in case another OOMError is thrown.
                    //Activate cache profiling to see which cache caused the error.
                    global.javaExecutionOptions.profileMemAdv = true;
                    printSummaryBox(rule, proofResults, successPaths, step, queue.size() + nextQueue.size() - v + 1);
                    throw e;
                    // DISABLE EXCEPTION CHECKSTYLE
                } catch (RuntimeException | AssertionError | StackOverflowError e) {
                    // ENABLE EXCEPTION CHECKSTYLE
                    logStep(step, v, term, true, alreadyLogged, initialTerm);
                    System.err.println("\n" +
                            "==========================================\n" +
                            "Top term when exception was thrown:\n" +
                            "==========================================\n");
                    printTermAndConstraint(term, false, initialTerm);
                    printSummaryBox(rule, proofResults, successPaths, step, queue.size() + nextQueue.size() - v + 1);
                    throw e;
                }
            }

            /* swap the queues */
            List<ConstrainedTerm> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();

            global.javaExecutionOptions.log = originalLog;
        }

        List<ConstrainedTerm> tweakedProofResults =
                printFormattedFailuresAndGetTweakedResults(initialTerm, proofResults);
        printSuccessFinalStates(initialTerm, successResults);
        printSuccessPCDiff(initialTerm, successResults);
        if (global.globalOptions.verbose) {
            printSummaryBox(rule, proofResults, successPaths, step, 0);
        }
        return tweakedProofResults;
    }

    /**
     * Print formatted failure final states, when {@code javaExecutionOptions.formatFailures} is true.
     *
     * @return proofResults, if {@code javaExecutionOptions.formatFailures} is false, otherwise get
     * {@code BoolToken.FALSE}
     */
    public List<ConstrainedTerm> printFormattedFailuresAndGetTweakedResults(ConstrainedTerm initialTerm,
                                                                            List<ConstrainedTerm> proofResults) {
        List<ConstrainedTerm> tweakedProofResults = proofResults;
        if (global.javaExecutionOptions.formatFailures && !proofResults.isEmpty() && prettyResult != null) {
            System.err.println("\n" +
                    "==========================================\n" +
                    "Failure final states:\n" +
                    "==========================================\n");
            for (ConstrainedTerm term : proofResults) {
                printTermAndConstraint(term, prettyResult, initialTerm);
            }
            tweakedProofResults = ImmutableList.of(new ConstrainedTerm(BoolToken.FALSE, initialTerm.termContext()));
        }
        return tweakedProofResults;
    }

    /**
     * Print formatted success final states, when {@code javaExecutionOptions.logSuccessFinalStates} is true.
     */
    public void printSuccessFinalStates(ConstrainedTerm initialTerm, List<ConstrainedTerm> successResults) {
        if (global.javaExecutionOptions.logSuccessFinalStates  && !successResults.isEmpty() && prettyResult != null) {
            System.err.println("\n" +
                    "==========================================\n" +
                    "Success final states:\n" +
                    "==========================================\n");
            for (ConstrainedTerm result : successResults) {
                printTermAndConstraint(result, prettyResult, initialTerm);
            }
        }
    }

    private void printSuccessPCDiff(ConstrainedTerm initialTerm, List<ConstrainedTerm> successResults) {
        if (global.javaExecutionOptions.logSuccessPCDiff && !successResults.isEmpty() && prettyResult != null) {
            System.out.println("\n" +
                    "==========================================\n" +
                    "Diff between initial path condition and final state path condition, success paths:\n" +
                    "==========================================\n");
            for (ConstrainedTerm result : successResults) {
                System.out.println(result.constraint().toStringNewElements(initialTerm.constraint()));
            }
        }
    }

    public void printTermAndConstraint(ConstrainedTerm term, boolean pretty,
                                       ConstrainedTerm initTerm) {
        //Disabling toString cache to minimise chance of OutOfMemoryError.
        boolean oldCacheToString = global.javaExecutionOptions.cacheToString;
        global.javaExecutionOptions.cacheToString = false;
        try {
            print(term.term(), pretty);
            printConstraint(term.constraint(), pretty, initTerm);
            System.err.println();
        } finally {
            global.javaExecutionOptions.cacheToString = oldCacheToString;
        }
    }

    private void printSummaryBox(Rule rule, List<ConstrainedTerm> proofResults, int successPaths, int step,
                                 int pathsInProgress) {
        if (pathsInProgress != 0) {
            System.err.format("\nSPEC ERROR: %s %s\n==================================\n" +
                            "Success execution paths: %d\nFailed execution paths: %d\nPaths in progress: %d\n",
                    new File(rule.getSource().source()), rule.getLocation(), successPaths, proofResults.size(),
                    pathsInProgress);
        } else if (proofResults != null) {
            if (proofResults.isEmpty()) {
                System.err.format("\nSPEC PROVED: %s %s\n==================================\nExecution paths: %d\n",
                        new File(rule.getSource().source()), rule.getLocation(), successPaths);
            } else {
                System.err.format("\nSPEC FAILED: %s %s\n==================================\n" +
                                "Success execution paths: %d\nFailed execution paths: %d\n",
                        new File(rule.getSource().source()), rule.getLocation(), successPaths, proofResults.size());
            }
        } else {
            System.err.print("\nEXECUTION FINISHED\n==================================\n");
        }
        System.err.format("Longest path: %d steps\n", step);
        global.profiler.printResult(true, global);
    }

    //map value = log format: true = pretty, false = toString()
    private Map<String, Boolean> cellsToLog = new LinkedHashMap<>();

    /**
     * null = do not print, false = toString, true = pretty.
     */
    private Boolean prettyPC;
    private Boolean prettyResult;
    private Boolean prettyInitTerm;
    private Boolean prettyTarget;

    private void parseLogCells() {
        for (String cell : global.javaExecutionOptions.logCells) {
            boolean pretty = false;
            if (cell.startsWith("(") && cell.endsWith(")")) {
                pretty = true;
                cell = cell.substring(1, cell.length() - 1);
            }
            switch (cell) {
            case "#pc":
                prettyPC = pretty;
                break;
            case "#result":
                prettyResult = pretty;
                break;
            case "#initTerm":
                prettyInitTerm = pretty;
                break;
            case "#target":
                prettyTarget = pretty;
                break;
            default:
                cellsToLog.put(cell, pretty);
                break;
            }
        }
    }

    private TimeMemoryEntry prevStats;

    /**
     * @param forced - if true, log this step when at least --log-basic is provided.
     * @param initTerm
     * @return whether it was actually logged
     */
    private boolean logStep(int step, int v, ConstrainedTerm term, boolean forced,
                            boolean alreadyLogged, ConstrainedTerm initTerm) {
        if (alreadyLogged || !global.javaExecutionOptions.logBasic) {
            return false;
        }
        global.profiler.logOverheadTimer.start();
        KItem top = (KItem) term.term();

        if (global.javaExecutionOptions.log || forced || global.javaExecutionOptions.logRulesPublic) {
            TimeMemoryEntry now = new TimeMemoryEntry(false);
            System.err.format("\nSTEP %d v%d : %s\n===================\n",
                    step, v, global.profiler.stepLogString(now, prevStats));
            prevStats = now;
        }

        boolean actuallyLogged = global.javaExecutionOptions.log || forced;
        if (actuallyLogged) {
            for (String cellName : cellsToLog.keySet()) {
                boolean pretty = cellsToLog.get(cellName);
                List<KItem> cells = getCells(top, "<" + cellName + ">");
                for (KItem cell : cells) {
                    print(cell, pretty);
                }
            }
            if (prettyPC != null) {
                printConstraint(term.constraint(), prettyPC, initTerm);
            }
        }
        global.profiler.logOverheadTimer.stop();
        return actuallyLogged;
    }

    private void print(K cell, boolean pretty) {
        if (pretty) {
            global.prettyPrinter.prettyPrint(cell, System.err);
        } else {
            System.err.println(toStringOrEmpty(cell));
        }
    }

    private void printConstraint(ConjunctiveFormula constraint, boolean pretty,
                                 ConstrainedTerm initTerm) {
        System.err.println("/\\");
        if (pretty) {
            global.prettyPrinter.prettyPrint(constraint, System.err);
        } else {
            System.err.println(constraint.toStringDifferentiated(initTerm.constraint()));
        }
    }

    private String toStringOrEmpty(Object o) {
        return o != null ? o.toString() : "";
    }

    private Pattern cellLabelPattern = Pattern.compile("<.+>|.+CellBag_");

    private List<KItem> getCells(KItem root, String label) {
        List<KItem> result = new ArrayList<>();
        collectCells(root, label, result);
        return result;
    }

    private void collectCells(KItemRepresentation root, String label, List<KItem> result) {
        if (root instanceof KItem && root.klabel().name().equals(label)) {
            result.add((KItem) root);
            return;
        }

        for (K child : root.klist().items()) {
            if ((child instanceof KItem && cellLabelPattern.matcher(((KItem) child).klabel().name()).matches())
                    || child instanceof BuiltinList/*child might be a bag of cells*/) {
                collectCells((KItemRepresentation) child, label, result);
            }
        }
    }

    /**
     * @return true if all boundary substitutions for {@code term} match the substitution on same position in
     * {@code targetBoundarySub}. False otherwise.
     * <p>
     * We consider 2 boundary substitutions to match if the equality {@code currentMatch ==K targetMatch} is not false.
     * That is, if the match contains symbolic terms,
     * and equality is neither true nor false, boundaryCellsMatchTarget will be true. This is because option
     * `--boundary-cells` is not designed to be used in conjunction with symbolic reasoning. Specification boundary
     * should not depend on symbolic values. And if we cannot decide if the boundary matches or not, we still want to
     * test if the full current term matches the target.
     */
    public boolean boundaryCellsMatchTarget(ConstrainedTerm term, Rule boundaryPattern,
                                            List<Substitution<Variable, Term>> targetBoundarySub, int step) {
        if (boundaryPattern == null) {
            return false;
        }
        if (global.javaExecutionOptions.logRulesPublic) {
            System.err.format("\nRegular rule match boundary phase, step %d\n" +
                    "==========================================\n", step);
        }
        List<Substitution<Variable, Term>> termBoundarySub = getBoundarySubstitution(term, boundaryPattern);
        if (targetBoundarySub.size() != termBoundarySub.size()) {
            throw KEMException.criticalError(String.format(
                    "Boundary pattern has different number of matches in current term and target.\n " +
                            "Current term: %s, target: %s", termBoundarySub, targetBoundarySub));
        }
        for (int i = 0; i < targetBoundarySub.size(); i++) {
            //Keeping term substitution as is and converting target substitution to equalities,
            //to build a simplifiable formula. In `simplify()` substitutions will be substituted into equalities,
            //and simplified if LHS == RHS.
            ConjunctiveFormula boundaryEq = ConjunctiveFormula.of(termBoundarySub.get(i),
                    PersistentUniqueList.from(targetBoundarySub.get(i).equalities(global)),
                    PersistentUniqueList.empty(), global);
            if (boundaryEq.simplify().isFalse()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Match the pattern, then in resulting substitutions keep only vars that start with "BOUND".
     * <p>
     * The result of pattern matching is a a list of substitutions, each having 2 kinds of variables:
     * <p>
     * 1. Cell body for cells mentioned in {@code KProveOptions.boundaryCells}. These vars will have the name
     * starting with {@code KProve.BOUNDARY_CELL_PREFIX}. They have to be preserved.
     * <p>
     * 2. The rest of the config. These will be anonymous vars with name starting with `_`.
     * <p>
     * It is a list because a pattern can match the same term in several ways. This function retains only the vars
     * from 1st category, in each substitution from the list.
     *
     * @see KProveOptions
     * @see KProve
     */
    public List<Substitution<Variable, Term>> getBoundarySubstitution(ConstrainedTerm term, Rule boundaryPattern) {
        List<Substitution<Variable, Term>> match = FastRuleMatcher.match(
                term.term(), boundaryPattern.leftHandSide(), term.termContext());
        List<Substitution<Variable, Term>> result = match.stream().map(sub ->
                ImmutableMapSubstitution.from(sub.entrySet().stream()
                        .filter(entry -> entry.getKey().name().startsWith(KProve.BOUNDARY_CELL_PREFIX))
                        .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue))))
                .collect(Collectors.toList());
        return result;
    }

    /**
     * Applies the first applicable specification rule and returns the result.
     */
    private ConstrainedTerm applySpecRules(ConstrainedTerm constrainedTerm, int step) {
        if (global.javaExecutionOptions.logRulesPublic) {
            System.err.format("\nSpec rule application phase, step %d\n" +
                    "==========================================\n", step);
        }
        //Work in progress: spec rules automaton. Use in for loop below.
        /*List<Pair<Rule, Integer>> automatonMatchedRules =
                theFastMatcher.matchWithAutomaton(constrainedTerm, definition.specAutomaton());

        if (global.javaExecutionOptions.logRulesPublic && !automatonMatchedRules.isEmpty()) {
            System.err.format("\nSpec rule application, rules matched by automaton: %d\n" +
                    "------------------------------------------\n", automatonMatchedRules.size());
        }*/

        //for (Pair<Rule, Integer> match : automatonMatchedRules) {
        for (Rule specRule : definition.specRulesPublic) {
            //Rule specRule = match.getLeft();
            ConstrainedTerm pattern = specRule.createLhsPattern(constrainedTerm.termContext());
            ConjunctiveFormula constraint = constrainedTerm.matchImplies(pattern, true, false,
                    new FormulaContext(FormulaContext.Kind.SpecRule, specRule, global), specRule.matchingSymbols());
            if (constraint != null) {
                if (global.javaExecutionOptions.logRulesPublic) {
                    System.err.format("\nSpec rule matched, building result for: %s %s\n-------------------------\n",
                            specRule.getSource(), specRule.getLocation());
                }
                global.stateLog.log(StateLog.LogEvent.SRULEATTEMPT, specRule.toKRewrite(), constrainedTerm.term(), constrainedTerm.constraint());
                ConstrainedTerm result = buildResult(specRule, constraint, null, true, constrainedTerm.termContext(),
                        new FormulaContext(FormulaContext.Kind.SpecConstr, specRule, global));
                if (result != null) {
                    global.stateLog.log(StateLog.LogEvent.SRULE, specRule.toKRewrite(), constrainedTerm.term(),
                            constrainedTerm.constraint(), result.term(), result.constraint());
                }
                if (global.javaExecutionOptions.logRulesPublic) {
                    if (result == null) {
                        System.err.println("Spec rule application: matched but failed to build result");
                    }
                    RuleSourceUtil.printRuleAndSource(specRule);
                }
                return result;
            }
        }
        return null;
    }

}

// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.strategies.TransitionCompositeStrategy;
import org.kframework.backend.java.util.Profiler;
import org.kframework.krun.api.SearchType;

public abstract class AbstractRewriter {

    protected final TermContext termContext;
    protected final TransitionCompositeStrategy strategy;
    protected int step;
    protected final List<Term> results = new ArrayList<>();
    protected RuleIndex ruleIndex;

    protected AbstractRewriter(Definition definition, TermContext termContext) {
        ruleIndex = definition.getIndex();
        this.termContext = termContext;
        this.strategy = new TransitionCompositeStrategy(definition.context().kompileOptions.transition);
    }

    public Term rewrite(Term subject, int bound) {
        for (step = 0; step != bound; ++step) {
            computeRewriteStep(subject, 1);
            Term result = getTransition(0);
            if (result != null) {
                subject = result;
            } else {
                break;
            }
        }

        return subject;
    }

    public Term rewrite(Term subject) {
        return rewrite(subject, -1);
    }

    /**
     * Gets the rules that could be applied to a given term according to the
     * rule indexing mechanism.
     *
     * @param term
     *            the given term
     * @return a list of rules that could be applied
     */
    protected final List<Rule> getRules(Term term) {
        Profiler.startTimer(Profiler.QUERY_RULE_INDEXING_TIMER);
        List<Rule> rules = ruleIndex.getRules(term);
        Profiler.stopTimer(Profiler.QUERY_RULE_INDEXING_TIMER);
        return rules;
    }

    protected final Term getTransition(int n) {
        return n < results.size() ? results.get(n) : null;
    }

    protected abstract void computeRewriteStep(Term subject, int successorBound);

    protected void computeRewriteStep(Term subject) {
        computeRewriteStep(subject, -1);
    }

    /**
     * Constructs the new subject term by applying the resulting substitution
     * map of pattern matching to the right-hand side of the rewrite rule.
     *
     * @param rule
     *            the rewrite rule
     * @param substitution
     *            a substitution map that maps variables in the left-hand side
     *            of the rewrite rule to sub-terms of the current subject term
     * @return the new subject term
     */
    protected abstract Term constructNewSubjectTerm(Rule rule, Map<Variable, Term> substitution);

    /**
     * Returns a list of substitutions obtained by matching the subject against
     * a rewrite rule.
     * <p>
     * This method is extracted to simplify the profiling script.
     * </p>
     */
    protected final List<Map<Variable,Term>> getMatchingResults(Term subject, Rule rule) {
        return PatternMatcher.patternMatch(subject, rule, termContext);
    }

    /**
    *
    * @param initialTerm
    * @param targetTerm not implemented yet
    * @param rules not implemented yet
    * @param pattern the pattern we are searching for
    * @param bound a negative value specifies no bound
    * @param depth a negative value specifies no bound
    * @param searchType defines when we will attempt to match the pattern

    * @return a list of substitution mappings for results that matched the pattern
    */
   public abstract List<Map<Variable,Term>> search(
           Term initialTerm,
           Term targetTerm,
           List<Rule> rules,
           Rule pattern,
           int bound,
           int depth,
           SearchType searchType);

}

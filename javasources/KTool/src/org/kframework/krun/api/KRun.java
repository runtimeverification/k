package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.krun.KRunExecutionException;

import edu.uci.ics.jung.graph.DirectedGraph;


public interface KRun {
	public KRunResult<KRunState> run(Term cfg) throws KRunExecutionException;
	public KRunResult<SearchResults> search(Integer bound, Integer depth, SearchType searchType, Rule pattern, Term cfg, RuleCompilerSteps compilationInfo) throws KRunExecutionException;
	public KRunResult<DirectedGraph<KRunState, Transition>> modelCheck(Term formula, Term cfg) throws KRunExecutionException;
	public KRunResult<KRunState> step(Term cfg, int steps) throws KRunExecutionException;
	public KRunDebugger debug(Term cfg) throws KRunExecutionException;
	public KRunDebugger debug(SearchResults searchResults);
}

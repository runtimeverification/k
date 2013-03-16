package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;

import edu.uci.ics.jung.graph.DirectedGraph;


public interface KRun {
	public KRunResult<KRunState> run(Term cfg) throws Exception;
	public KRunResult<SearchResults> search(Integer bound, Integer depth, SearchType searchType, Rule pattern, Term cfg, RuleCompilerSteps compilationInfo) throws Exception;
	public KRunResult<DirectedGraph<KRunState, Transition>> modelCheck(Term formula, Term cfg) throws Exception;
	public KRunResult<KRunState> step(Term cfg, int steps) throws Exception;
	public KRunDebugger debug(Term cfg) throws Exception;
	public KRunDebugger debug(SearchResults searchResults);
}

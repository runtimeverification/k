package org.kframework.krun.api;

import org.kframework.kil.*;

import edu.uci.ics.jung.graph.DirectedGraph;

import java.util.Set;

public interface KRun {
	public KRunResult<KRunState> run(Term cfg) throws Exception;
	public KRunResult<SearchResults> search(Integer bound, Integer depth, SearchType searchType, Rule pattern, Term cfg, Set<String> varNames) throws Exception;
	public KRunResult<DirectedGraph<KRunState, Transition>> modelCheck(Term formula, Term cfg) throws Exception;
	public KRunResult<KRunState> step(Term cfg, int steps) throws Exception;
	public KRunDebugger debug(Term cfg) throws Exception;
	public KRunDebugger debug(SearchResults searchResults);
}

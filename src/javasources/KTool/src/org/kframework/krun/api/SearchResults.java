package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.K;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

public class SearchResults {
	private List<SearchResult> solutions;
	private DirectedGraph<KRunState, Transition> graph;
	private boolean isDefaultPattern;
	
	protected Context context;

	public SearchResults(List<SearchResult> solutions, DirectedGraph<KRunState, Transition> graph, boolean isDefaultPattern, Context context) {
		this.context = context;
		this.solutions = solutions;
		this.graph = graph;
		this.isDefaultPattern = isDefaultPattern;
	}

	@Override
	public String toString() {
    HashSet<String> solutionSet = new HashSet<String>();
		for (SearchResult solution : solutions) {
			Map<String, Term> substitution = solution.getSubstitution();
			if (isDefaultPattern) {
				UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
				substitution.get("B:Bag").accept(unparser);
        solutionSet.add(unparser.getResult());
				//sb.append("\n" + unparser.getResult());
			} else {
				boolean empty = true;
				
				for (String variable : substitution.keySet()) {
					UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
					//sb.append("\n" + variable + " -->");
					substitution.get(variable).accept(unparser);
					//sb.append("\n" + unparser.getResult());
          solutionSet.add(variable + " -->\n" + unparser.getResult());
					empty = false;
				}
				if (empty) {
          solutionSet.add("Empty subsitution");
					//sb.append("\nEmpty substitution");
				}
			}
		}
		StringBuilder sb = new StringBuilder();
		sb.append("Search results:");
    int i = 1;
    for (String string : solutionSet) {
      sb.append("\n\nSolution " + i + ":\n" + string);
      i++;
    }
		if (i == 1) {
			sb.append("\nNo search results");
		}
		return sb.toString();
	}

	public DirectedGraph<KRunState, Transition> getGraph() {
		return graph;
	}

	public List<SearchResult> getSolutions() {
		return solutions;
	}
}

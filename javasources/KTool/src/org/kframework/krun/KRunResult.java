package org.kframework.krun;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.krun.runner.KRunner;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import edu.uci.ics.jung.graph.DirectedGraph;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class KRunResult {

	private Term result = null;
	private List<Map<String, Term>> searchResults = null;
	private Set<String> varNames = null;
	private List<Transition> initialPath = null;
	private List<Transition> loop = null;
	private String statistics;
	private boolean isDefaultPattern;
	private Term rawResult;
	private List<Term> rawSearchResults;

	public KRunResult(Term result, Term rawResult) {
		this.result = result;
		this.rawResult = rawResult;
	}
	public KRunResult(List<Map<String, Term>> searchResults, List<Map<String, Term>> rawSearchSubstitution, Rule pattern, boolean isDefaultPattern, Set<String> varNames) throws TransformerException {
		this.searchResults = searchResults;
		this.isDefaultPattern = isDefaultPattern;
		this.varNames = varNames;
		this.rawSearchResults = new ArrayList<Term>();
		for (Map<String, Term> searchResult : rawSearchSubstitution) {
			this.rawSearchResults.add((Term) pattern.getBody().accept(new SubstitutionFilter(searchResult)));
		}
	}
	public KRunResult(List<Transition> initialPath, List<Transition> loop) {
		this.initialPath = initialPath;
		this.loop = loop;
	}

	public void setStatistics(String statistics) {
		this.statistics = statistics;
	}

	public List<String> prettyPrint() {
		if (result != null) {
			UnparserFilter unparser = new UnparserFilter(true, K.color);
			result.accept(unparser);
			List<String> l = new ArrayList<String>();
			l.add(unparser.getResult());
			if (K.statistics) {
				l.add(statistics);
			}
			return l;
		} else if (searchResults != null) {
			int i = 1;
			List<String> l = new ArrayList<String>();
			for (Map<String, Term> searchResult : searchResults) {
				l.add("\nSolution " + i + ":");
				if (isDefaultPattern) {
					UnparserFilter unparser = new UnparserFilter(true, K.color);
					searchResult.get("B:Bag").accept(unparser);
					l.add(unparser.getResult());
				} else {
					boolean empty = true;
					for (String variable : searchResult.keySet()) {
						String varName = variable.substring(0, variable.indexOf(":"));
						if (varNames.contains(varName)) {
							UnparserFilter unparser = new UnparserFilter(true, K.color);
							l.add(variable + " -->");
							searchResult.get(variable).accept(unparser);
							l.add(unparser.getResult());
							empty = false;
						}
					}
					if (empty) {
						l.add("Empty substitution");
					}
				}
				i++;
			}
			if (l.size() == 0) {
				l.add("\nNo search results");
			}
			return l;
		} else if (initialPath != null && loop != null) {
			List<String> l = new ArrayList<String>();
			l.add("Path from initial state to beginning of cycle:");
			for (Transition trans : initialPath) {
				l.add("\nLabel: " + trans.getLabel());
				UnparserFilter unparser = new UnparserFilter(true, K.color);
				trans.getTerm().accept(unparser);
				l.add(unparser.getResult());
			}
			if (initialPath.size() == 0) {
				l.add("Empty path");
			}
			l.add("Path of cycle:");
			for (Transition trans : loop) {
				l.add("\nLabel: " + trans.getLabel());
				UnparserFilter unparser = new UnparserFilter(true, K.color);
				trans.getTerm().accept(unparser);
				l.add(unparser.getResult());
			}
			if (loop.size() == 0) {
				l.add("Empty path");
			}
			return l;
		}
		throw new RuntimeException("should be unreachable");
	}

	public Term getResult() {
		return this.result;
	}

	public Term getRawResult() {
		return this.rawResult;
	}

	public List<Map<String, Term>> getSearchResults() {	
		return this.searchResults;
	}

	private String rawOutput;

	public void setRawOutput(String rawOutput) {
		this.rawOutput = rawOutput;
	}
	
	public String rawOutput() {
		return rawOutput;
	}

	private DirectedGraph<KRunResult, RuleInvocation> searchGraph;
	public void setSearchGraph(DirectedGraph<KRunResult, RuleInvocation> searchGraph) {
		this.searchGraph = searchGraph;
	}

	public DirectedGraph<KRunResult, RuleInvocation> getSearchGraph() {
		return searchGraph;
	}

	public String searchGraph() {
		return searchGraph.toString();
	}

	public KRunResult get(String num) throws Exception {
		int solutionNum = Integer.parseInt(num);
		Map<String, Term> subst = this.searchResults.get(solutionNum - 1) ;
		if(isDefaultPattern) {
			return new KRunResult(subst.get("B:Bag"), this.rawSearchResults.get(solutionNum - 1));
		} else {
			throw new Exception("Can't call get() with custom search pattern yet");
		}
	}

	@Override
	public String toString() {
		UnparserFilter unparser = new UnparserFilter(true, K.color);
		result.accept(unparser);
		return "\nNode " + nodeId + ":\n" + unparser.getResult();
	}

	private int nodeId;
	public int getNodeId() {
		return nodeId;
	}

	public void setNodeId(int nodeId) {
		this.nodeId = nodeId;
	}
}

package org.kframework.krun;

import org.kframework.backend.unparser.UnparserFilter;
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

	public KRunResult(Term result) {
		this.result = result;
	}
	public KRunResult(List<Map<String, Term>> searchResults, boolean isDefaultPattern, Set<String> varNames) {
		this.searchResults = searchResults;
		this.isDefaultPattern = isDefaultPattern;
		this.varNames = varNames;
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

	private String rawOutput;

	public void setRawOutput(String rawOutput) {
		this.rawOutput = rawOutput;
	}
	
	public String rawOutput() {
		return rawOutput;
	}

	private String searchGraph;
	public void setSearchGraph(String searchGraph) {
		this.searchGraph = searchGraph;
	}

	public String searchGraph() {
		return searchGraph;
	}

}

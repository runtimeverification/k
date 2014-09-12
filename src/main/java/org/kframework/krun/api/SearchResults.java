// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;

import org.kframework.backend.unparser.UnparserFilterNew;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;

import java.util.TreeSet;
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
        TreeSet<String> solutionStrings = new TreeSet<String>();
        for (SearchResult solution : getSolutions()) {
            Map<String, Term> substitution = solution.getSubstitution();
            if (isDefaultPattern()) {
                UnparserFilterNew unparser = new UnparserFilterNew(true, context.colorOptions.color(),
                        context.krunOptions.output, false, context);
                unparser.visitNode(substitution.get("B:Bag"));
                solutionStrings.add("\n" + unparser.getResult());
            } else {
                boolean empty = true;

                StringBuilder varStringBuilder = new StringBuilder();
                for (String variable : substitution.keySet()) {
                    UnparserFilterNew unparser = new UnparserFilterNew(true, context.colorOptions.color(),
                            context.krunOptions.output, false, context);
                    unparser.visitNode(substitution.get(variable));
                    varStringBuilder.append("\n" + variable + " -->\n" + unparser.getResult());
                    empty = false;
                }
                if (empty) {
                    solutionStrings.add("\nEmpty substitution");
                } else {
                    solutionStrings.add(varStringBuilder.toString());
                }
            }
        }
        StringBuilder sb = new StringBuilder();
        sb.append("Search results:");
        if (solutionStrings.isEmpty()) {
            sb.append("\nNo search results");
        } else {
            int i = 1;
            for (String string : solutionStrings) {
                sb.append("\n\nSolution " + i + ":" + string);
                i++;
            }
        }

        return sb.toString();
    }

    public DirectedGraph<KRunState, Transition> getGraph() {
        return graph;
    }

    public List<SearchResult> getSolutions() {
        return solutions;
    }

    public boolean isDefaultPattern(){

        return this.isDefaultPattern;
    }
}

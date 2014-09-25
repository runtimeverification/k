// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;

import java.util.List;

public class SearchResults {
    private List<SearchResult> solutions;
    private DirectedGraph<KRunState, Transition> graph;
    private boolean isDefaultPattern;

    public SearchResults(List<SearchResult> solutions, DirectedGraph<KRunState, Transition> graph, boolean isDefaultPattern) {
        this.solutions = solutions;
        this.graph = graph;
        this.isDefaultPattern = isDefaultPattern;
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

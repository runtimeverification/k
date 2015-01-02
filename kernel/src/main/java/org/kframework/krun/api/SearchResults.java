// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;

import java.util.List;

public class SearchResults implements KRunResult {
    private List<SearchResult> solutions;
    private DirectedGraph<KRunState, Transition> graph;

    public SearchResults(List<SearchResult> solutions, DirectedGraph<KRunState, Transition> graph) {
        this.solutions = solutions;
        this.graph = graph;
    }

    public DirectedGraph<KRunState, Transition> getGraph() {
        return graph;
    }

    public List<SearchResult> getSolutions() {
        return solutions;
    }
}

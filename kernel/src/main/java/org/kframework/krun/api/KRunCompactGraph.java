// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedOrderedSparseMultigraph;
import edu.uci.ics.jung.graph.util.Pair;
import org.apache.commons.collections4.BidiMap;
import org.apache.commons.collections4.bidimap.DualHashBidiMap;
import org.kframework.krun.api.Transition.TransitionType;

import java.util.Map.Entry;

public class KRunCompactGraph extends KRunGraph {
    private BidiMap<Integer, KRunState> states;

    public KRunCompactGraph() {
        super();
        states = new DualHashBidiMap<>();
    }

    public KRunCompactGraph(KRunGraph graph) {
        for (KRunState vertex : graph.getVertices()) {
            addVertex(vertex);
        }
        for (Transition edge : graph.getEdges()) {
            KRunState source = canonicalizeState(graph.getSource(edge));
            KRunState dest = canonicalizeState(graph.getDest(edge));
            addEdge(edge,source, dest);
        }
    }

    @Override
    public boolean addVertex(KRunState vertex) {
        return putState(vertex) && super.addVertex(vertex);
    }

    @Override
    public boolean addEdge(Transition transition, KRunState v1, KRunState v2) {
        v1 = canonicalizeState(v1);
        v2 = canonicalizeState(v2);
        Transition t = findEdge(v1, v2);
        if (t != null) return false;
        return super.addEdge(transition, v1, v2);
    }

    /**
     * Adds the new state to the states map
     * @param state new state to add
     * @return if the stated wasn't previously in the states map return true else return false
     */
    public boolean putState(KRunState state) {
        if(!states.containsValue(state)){
            states.put(state.getStateId(), state);
            return true;
        }
        return false;
    }

    public boolean containsState(int id) {
        return states.containsKey(id);
    }

    public KRunState getState(int stateNum) {
        KRunState state = states.get(stateNum);
        if (state == null) throw new IllegalArgumentException("State " + stateNum + " does not exist in the graph.");
        return state;
    }


    public void mergeSearchGraph(DirectedGraph<KRunState, Transition> graphFragment) {
        for (KRunState state : graphFragment.getVertices()) {
            //check if graph already contains state
            Entry<Integer, KRunState> prevValue = containsValue(state);
            if (prevValue==null) {
                putState(state);
                addVertex(state);
            }
        }
        for (Transition edge : graphFragment.getEdges()) {
            Pair<KRunState> vertices = graphFragment.getEndpoints(edge);
            Transition existingEdge = findEdge(vertices.getFirst(), vertices.getSecond());
            KRunState first =vertices.getFirst();
            KRunState second = vertices.getSecond();
            //if graph already contained state used old state
            Entry<Integer, KRunState> prevValue = containsValue(first);
            if (prevValue!=null){
                first = prevValue.getValue();
            }
            prevValue = containsValue(second);
            if(prevValue!=null){
                second = prevValue.getValue();
            }
            if (existingEdge != null && existingEdge.getType() == TransitionType.UNLABELLED) {
                removeEdge(existingEdge);
                addEdge(edge, first, second);
            } else if (existingEdge == null) {
                addEdge(edge, first, second);
            }
        }
    }

    /* checks if state already exists(using Semantic equal)
     * if it exists return old value
     * this intends to replace states.containsValue which uses hash and equals defined in KRunState
     */
    public Entry<Integer, KRunState> containsValue(KRunState state){
        for (Entry<Integer,KRunState> e : states.entrySet() ){
            if(state.equals(e.getValue()))
                return e ;
        }
        return null;
    }

    public KRunState canonicalizeState(KRunState state) {
        int stateNum = states.getKey(state);
        return states.get(stateNum);
    }


}

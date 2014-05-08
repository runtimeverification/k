package org.kframework.krun.api;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class KRunGraph extends DirectedSparseGraph<KRunState, Transition> {
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Vertices:\n");
        List<KRunState> sorted = new ArrayList<>(getVertices());
        Collections.sort(sorted);
        for (KRunState state : sorted) {
            sb.append(state.toString(true));
        }
        sb.append("\n\nEdges:\n");
        for (Transition trans : getEdges()) {
            sb.append(trans.toString());
            sb.append(" [Node ");
            sb.append(getSource(trans).getStateId());
            sb.append(", Node ");
            sb.append(getDest(trans).getStateId());
            sb.append("]");
        }
        return sb.toString();
    }

}

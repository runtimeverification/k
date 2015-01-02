// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.transformation.Transformation;
import org.kframework.utils.inject.InjectGeneric;

import com.google.inject.Inject;

public class PrintKRunGraph implements Transformation<KRunGraph, String> {

    @InjectGeneric private Transformation<KRunState, String> statePrinter;
    @InjectGeneric private Transformation<Transition, String> transitionPrinter;

    @Inject
    public PrintKRunGraph() {}

    public PrintKRunGraph(
            Transformation<KRunState, String> statePrinter,
            Transformation<Transition,  String> transitionPrinter) {
        this.statePrinter = statePrinter;
        this.transitionPrinter = transitionPrinter;
    }

    @Override
    public String run(KRunGraph graph, Attributes a) {
        StringBuilder sb = new StringBuilder();
        sb.append("Vertices:\n");
        List<KRunState> sorted = new ArrayList<>(graph.getVertices());
        Collections.sort(sorted);
        for (KRunState state : sorted) {
            sb.append("\nNode " + state.getStateId() + ":\n");
            sb.append(statePrinter.run(state, a));
        }
        sb.append("\n\nEdges:\n");
        a.add(KRunGraph.class, graph);
        a.add(Boolean.class, PrintTransition.PRINT_VERBOSE_GRAPH, false);
        for (Transition trans : graph.getEdges()) {
            sb.append(transitionPrinter.run(trans, a));
        }
        return sb.toString();
    }

    @Override
    public String getName() {
        return "print search graph";
    }

}

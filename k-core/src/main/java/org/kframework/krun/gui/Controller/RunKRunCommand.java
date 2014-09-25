// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.Controller;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.krun.tools.Debugger;
import edu.uci.ics.jung.graph.DirectedGraph;

public class RunKRunCommand {

    private final Term initialConfiguration;
    protected final Context context;
    protected final Debugger debugger;

    public RunKRunCommand(Term initialConfiguration, Debugger debugger, Context context) throws KRunExecutionException {
        super();
        this.context = context;
        this.initialConfiguration = initialConfiguration;
        this.debugger = debugger;
    }

    public RunKRunCommand(KRunState state, Debugger debugger, Context context) {
        super();
        this.context = context;
        this.initialConfiguration = state.getRawResult();
        this.debugger = debugger;
        KRunGraph dg = new KRunGraph();
        dg.addVertex(state);
    }

    public DirectedGraph<KRunState, Transition> firstStep() {
        return debugger.getGraph();
    }

    public DirectedGraph<KRunState, Transition> step(KRunState v, int steps) throws KRunExecutionException {
        if (steps > 0) {
            debugger.setCurrentState(v.getStateId());
            debugger.step(steps);
        }
        return debugger.getGraph();
    }

    public DirectedGraph<KRunState, Transition> step_all(int steps, KRunState v) throws KRunExecutionException {
        if (steps < 1)
            steps = 1;
        debugger.setCurrentState(v.getStateId());
        debugger.stepAll(steps);
        return debugger.getGraph();
    }

    public DirectedGraph<KRunState, Transition> getCurrentGraph() {
        return debugger.getGraph();
    }

    public Debugger getDebugger() {
        return debugger;
    }

    public Context getContext() {
        return context;
    }

    public static String transformTerm(Term term, Context context) {
        term = KRunState.concretize(term, context);
        if (term.getClass() == Cell.class) {
            Cell generatedTop = (Cell) term;
            if (generatedTop.getLabel().equals("generatedTop")) {
                term = generatedTop.getContents();
            }
        }

        UnparserFilter unparser = new UnparserFilter(true, false, context);
        unparser.visitNode(term);
        return unparser.getResult();
    }

}

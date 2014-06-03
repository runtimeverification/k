// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.Controller;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;

import edu.uci.ics.jung.graph.DirectedGraph;

public class RunKRunCommand {

    protected Term initialConfiguration;
    protected Context context;
    protected KRun krun;
    protected KRunDebugger debugger;

    public RunKRunCommand(Term initialConfiguration, KRun krun, Context context) throws KRunExecutionException {
        super();
        this.context = context;
        this.initialConfiguration = initialConfiguration;
        this.krun = krun;
        debugger = krun.debug(initialConfiguration);
    }

    public RunKRunCommand(KRunState state, KRun krun, Context context) {
        super();
        this.context = context;
        this.initialConfiguration = state.getRawResult();
        this.krun = krun;
        DirectedGraph<KRunState, Transition> dg = new KRunGraph();
        dg.addVertex(state);
        debugger = krun.debug(dg);
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
    public KRun getKrun() {
        return krun;
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

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.Controller;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.K;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.Main;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class RunKRunCommand {

    protected Term KAST;
    protected String lang;
    protected Context context;
    protected KRun krun;
    protected KRunDebugger debugger;
    protected RunProcess rp;

    public RunKRunCommand(Term kast, String lang, KRun krun, Context context) throws KRunExecutionException {
        super();
        this.context = context;
        this.KAST = kast;
        this.lang = lang;
        rp = new RunProcess();
        this.krun = krun;
        Term cfg;
        cfg = Main.makeConfiguration(KAST, null, rp, K.term, context);
        debugger = krun.debug(cfg);
    }

    public RunKRunCommand(KRunState state, String lang, KRun krun, Context context) {
        super();
        this.context = context;
        this.KAST = state.getRawResult();
        this.lang = lang;
        rp = new RunProcess();
        this.krun = krun;
        DirectedGraph<KRunState, Transition> dg = new DirectedSparseGraph<KRunState, Transition>();
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

    public String getLang() {
        return lang;
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

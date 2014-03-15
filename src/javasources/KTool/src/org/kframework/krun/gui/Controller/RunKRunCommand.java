package org.kframework.krun.gui.Controller;

import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.backend.maude.krun.MaudeKRun;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.krun.K;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.Main;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.utils.Stopwatch;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class RunKRunCommand {

    protected Term KAST;
    protected String lang;
    protected Context context;
    protected KRun krun;
    protected KRunDebugger debugger;
    protected RunProcess rp;

    public RunKRunCommand(Term kast, String lang, Context context) throws Exception {
        super();
        this.context = context;
        this.KAST = kast;
        this.lang = lang;
        rp = new RunProcess();
        this.krun = createKrun(context);
        Term cfg;
        cfg = Main.makeConfiguration(KAST, null, rp, K.term != null, context);
        debugger = krun.debug(cfg);
    }

    public RunKRunCommand(KRunState state, String lang, Context context) throws Exception {
        super();
        this.context = context;
        this.KAST = state.getRawResult();
        this.lang = lang;
        rp = new RunProcess();
        this.krun = createKrun(context);
        DirectedGraph<KRunState, Transition> dg = new DirectedSparseGraph<KRunState, Transition>();
        dg.addVertex(state);
        debugger = krun.debug(dg);
    }

    public DirectedGraph<KRunState, Transition> firstStep() throws Exception {
        return debugger.getGraph();
    }

    public void abort() {
        System.exit(0);
    }

    public DirectedGraph<KRunState, Transition> step(KRunState v, int steps) throws Exception {
        if (steps > 0) {
            debugger.setCurrentState(v.getStateId());
            debugger.step(steps);
        }
        return debugger.getGraph();
    }

    public DirectedGraph<KRunState, Transition> step_all(int steps, KRunState v) throws Exception {
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

    private static KRun createKrun(Context context) {
        KRun krun;
        if (K.backend.equals("maude")) {
            krun = new MaudeKRun(context, Stopwatch.instance());
        } else if (K.backend.equals("java")) {
            try {
                krun = new JavaSymbolicKRun(context);
            } catch (KRunExecutionException e) {
                org.kframework.utils.Error.report(e.getMessage());
                return null;
            }
        } else {
            org.kframework.utils.Error
                    .report("Currently supported backends are 'maude' and 'java'");
            return null;
        }
        krun.setBackendOption("io", false);
        return krun;
    }

    public static String transformTerm(Term term, Context context) {
        try {
            term = (Term) term.accept(new ConcretizeSyntax(context));
            term = (Term) term.accept(new TypeInferenceSupremumFilter(context));
            term = (Term) term.accept(new BestFitFilter(
                    new GetFitnessUnitTypeCheckVisitor(context), context));
            // as a last resort, undo concretization
            term = (Term) term
                    .accept(new org.kframework.krun.FlattenDisambiguationFilter(context));
        } catch (TransformerException e) {
            e.printStackTrace();
        }
        if (term.getClass() == Cell.class) {
            Cell generatedTop = (Cell) term;
            if (generatedTop.getLabel().equals("generatedTop")) {
                term = generatedTop.getContents();
            }
        }

        UnparserFilter unparser = new UnparserFilter(true, false, context);
        term.accept(unparser);
        return unparser.getResult();
    }

}

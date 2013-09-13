package org.kframework.krun.gui.Controller;

import java.io.IOException;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.krun.K;
import org.kframework.krun.Main;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.Transition;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;

import edu.uci.ics.jung.graph.DirectedGraph;

public class RunKRunCommand {

        protected Term KAST;
        protected String lang;
        boolean isSwitch;

        KRun krun ;
        KRunDebugger debugger;
        RunProcess rp ;
        
        public RunKRunCommand(Term kast, String lang, boolean isSwitch, KRun krun)
                        throws IOException {
                super();
                this.KAST = kast;
                this.lang = lang;
                this.isSwitch = isSwitch;
                rp = new RunProcess();
                this.krun = krun;
        }

        public DirectedGraph<KRunState, Transition> firstStep(Context context) throws Exception{
                Term cfg = Main.makeConfiguration(KAST, null, rp, K.term!=null, context);
                debugger = krun.debug(cfg);
                return debugger.getGraph();
        }

        public void abort() {
                System.exit(0);
        }
        
        public DirectedGraph<KRunState, Transition>  step(KRunState v , int steps) throws Exception {
                if (steps > 0 ){
                        debugger.setCurrentState(v.getStateId());
                        debugger.step(steps);
                }
                return debugger.getGraph();
        }

        public DirectedGraph<KRunState, Transition> step_all(int steps, KRunState v) throws Exception {
                if (steps < 1)
                        steps = 1;
                debugger.setCurrentState(v.getStateId());
                SearchResults states = debugger.stepAll(steps);
                return debugger.getGraph();
        }
        
        public static String transformTerm (Term term, Context context) {
                try {
                        term = (Term) term.accept(new ConcretizeSyntax(context));
                        term = (Term) term.accept(new TypeInferenceSupremumFilter(context));
                        term = (Term) term.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context),
                    context));
                        //as a last resort, undo concretization
                        term = (Term) term.accept(new org.kframework.krun.FlattenDisambiguationFilter(context));
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
        
        public DirectedGraph<KRunState,Transition> getCurrentGraph (){
                return debugger.getGraph();
        }
}

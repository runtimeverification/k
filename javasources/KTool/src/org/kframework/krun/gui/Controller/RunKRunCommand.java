package org.kframework.krun.gui.Controller;

import java.io.IOException;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.krun.K;
import org.kframework.krun.Main;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.MaudeKRun;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.Transition;
import org.kframework.krun.gui.UIDesign.ColorVisitor;
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
	
	public RunKRunCommand(Term kast, String lang, boolean isSwitch)
			throws IOException {
		super();
		this.KAST = kast;
		this.lang = lang;
		this.isSwitch = isSwitch;
		krun = new MaudeKRun();
		rp = new RunProcess();
	}

	public DirectedGraph<KRunState, Transition> firstStep() throws Exception{
		Term cfg = Main.makeConfiguration(KAST, null, rp, K.term!=null);
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

	public static void seeTerm(Term c){
		MaudeFilter mf = new MaudeFilter();
		c.accept(mf);
		String rez = mf.getResult();
	}
	
	public static String transformTerm (Term term ) {
		try {
			term = (Term) term.accept(new ConcretizeSyntax());
			term = (Term) term.accept(new TypeInferenceSupremumFilter());
			term = (Term) term.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
			//as a last resort, undo concretization
			term = (Term) term.accept(new org.kframework.krun.FlattenDisambiguationFilter());
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		if (term.getClass() == Cell.class) {
			Cell generatedTop = (Cell) term;
			if (generatedTop.getLabel().equals("generatedTop")) {
				term = generatedTop.getContents();
			}
		}
		//set the color map  
		ColorVisitor cv = new ColorVisitor();
		term.accept(cv);
		
		UnparserFilter unparser = new UnparserFilter(true, false);
		term.accept(unparser);
		return unparser.getResult();
	}
	
	public DirectedGraph<KRunState,Transition> getCurrentGraph (){
		return debugger.getGraph();
	}
}

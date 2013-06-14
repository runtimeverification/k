package org.kframework.krun.gui.Controller;

import java.io.IOException;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
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
import org.kframework.utils.XmlLoader;
import org.w3c.dom.Document;

import edu.uci.ics.jung.graph.DirectedGraph;

/**
 * Class that acts as a gateway between the KRunDebugger and GUI.
 * 
 * @author danielV
 * 
 */
@SuppressWarnings("unused")
public class RunKRunCommand {
  private static final String ERROR_MESSAGE = "Debugger not started! Call firstStep to start debugger.";
  private Term KAST;
  private String lang;
  public static DefinitionHelper definitionHelper;
  private KRun krun;
  private KRunDebugger debugger;
  private RunProcess rp;
  private boolean makeConf;

  public RunKRunCommand(Term kast, String lang, DefinitionHelper definitionHelper, boolean makeConf)
          throws IOException {
    super();
    this.KAST = kast;
    this.lang = lang;
    krun = new MaudeKRun(definitionHelper);
    RunKRunCommand.definitionHelper = definitionHelper;
    rp = new RunProcess();
    this.makeConf = makeConf;
  }

  public DirectedGraph<KRunState, Transition> firstStep(DefinitionHelper definitionHelper)
          throws Exception {
    Term cfg;
    if (makeConf) {
      cfg = Main.makeConfiguration(KAST, null, rp, K.term != null, definitionHelper);
    }
    else {
      cfg = KAST;
    }
    debugger = krun.debug(cfg);
    return debugger.getGraph();
  }

  public DirectedGraph<KRunState, Transition> step(KRunState state, int steps) throws Exception {
    System.out.println(transformTerm(state.getRawResult()));
    String parsed = org.kframework.parser.concrete.KParser.ParseKConfigString(transformTerm(state
            .getRawResult()));
    Document doc = XmlLoader.getXMLDoc(parsed);
    if (debugger == null)
      throw new IllegalStateException(ERROR_MESSAGE);
    if (steps > 0) {
      debugger.setCurrentState(state.getStateId());
      debugger.step(steps);
    }
    return debugger.getGraph();
  }

  public DirectedGraph<KRunState, Transition> step_all(int steps, KRunState v) throws Exception {
    if (debugger == null)
      throw new IllegalStateException(ERROR_MESSAGE);
    if (steps < 1)
      steps = 1;
    debugger.setCurrentState(v.getStateId());
    SearchResults states = debugger.stepAll(steps);
    return debugger.getGraph();
  }

  public DirectedGraph<KRunState, Transition> getCurrentGraph() throws Exception {
    if (debugger == null)
      throw new IllegalStateException(ERROR_MESSAGE);
    return debugger.getGraph();
  }

  public void abort() {
    System.exit(0);
  }

  public static String transformTerm(Term term, DefinitionHelper definitionHelper) {
    synchronized (RunKRunCommand.class) {
      if (term == null)
        return null;
      try {
        term = (Term) term.accept(new ConcretizeSyntax(definitionHelper));
        term = (Term) term.accept(new TypeInferenceSupremumFilter(definitionHelper));
        term = (Term) term.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(
                definitionHelper), definitionHelper));
        // as a last resort, undo concretization
        term = (Term) term.accept(new org.kframework.krun.FlattenDisambiguationFilter(
                definitionHelper));
      } catch (TransformerException e) {
        e.printStackTrace();
      }
      if (term.getClass() == Cell.class) {
        Cell generatedTop = (Cell) term;
        if (generatedTop.getLabel().equals("generatedTop")) {
          term = generatedTop.getContents();
        }
      }
      // set the color map
      ColorVisitor cv = new ColorVisitor(definitionHelper);
      term.accept(cv);
      UnparserFilter unparser = new UnparserFilter(true, false, definitionHelper);
      term.accept(unparser);
      return unparser.getResult();
    }
  }

  public static String transformTerm(Term term) {
    return transformTerm(term, definitionHelper);
  }

}

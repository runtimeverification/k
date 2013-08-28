package org.kframework.krun.api;

import java.util.Set;

import org.apache.commons.collections15.BidiMap;
import org.apache.commons.collections15.bidimap.DualHashBidiMap;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.K;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.Transition.TransitionType;
import org.kframework.parser.DefinitionLoader;
import org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.util.Pair;

public class KRunApiDebugger implements KRunDebugger {
	private KRun krun;
	private Integer currentState;
	private DirectedGraph<KRunState, Transition> graph;
	private BidiMap<Integer, KRunState> states;

	private static Rule defaultPattern;
	private static Set<String> defaultVars;
	private static RuleCompilerSteps defaultPatternInfo;
	
	protected Context context;

	public KRunApiDebugger(KRun krun, Term cfg, Context context) throws KRunExecutionException {
		this.context = context;
		try { 
			org.kframework.parser.concrete.KParser.ImportTbl(K.compiled_def + "/def/Concrete.tbl");
			ASTNode pattern = DefinitionLoader.parsePattern(K.pattern, "Command line pattern",
                    context);
			CollectVariablesVisitor vars = new CollectVariablesVisitor(context);
			pattern.accept(vars);
			defaultVars = vars.getVars().keySet();
			defaultPatternInfo = new RuleCompilerSteps(K.definition, context);
			pattern = defaultPatternInfo.compile(new Rule((Sentence) pattern), null);

			defaultPattern = (Rule) pattern;
		} catch (Exception e) {
			e.printStackTrace();
		}

		this.krun = krun;
		KRunState initialState = new KRunState(cfg, K.stateCounter++, context);
		graph = new DirectedSparseGraph<KRunState, Transition>();
		graph.addVertex(initialState);
		states = new DualHashBidiMap<Integer, KRunState>();
		putState(initialState);
		KRunState reduced = krun.step(cfg, 0).getResult();
		reduced.setStateId(K.stateCounter++);
		putState(reduced);
		graph.addVertex(reduced);
		graph.addEdge(Transition.reduce(context), initialState, reduced);
		currentState = reduced.getStateId();
	}

	public KRunApiDebugger(KRun krun, DirectedGraph<KRunState, Transition> graph) {
		this.krun = krun;
		this.currentState = null;
		this.graph = graph;
		states = new DualHashBidiMap<Integer, KRunState>();
		for (KRunState state : graph.getVertices()) {
			putState(state);
		}
	}

	private void putState(KRunState state) {
		states.put(state.getStateId(), state);
	}

	public DirectedGraph<KRunState, Transition> getGraph() {
		return graph;
	}

	public Integer getCurrentState() {
		return currentState;
	}

	public void setCurrentState(Integer stateNum) throws IllegalArgumentException {
		if (stateNum == null || states.containsKey(stateNum)) {
			currentState = stateNum;
		} else {
			throw new IllegalArgumentException("Must set current state to a state number already in the graph.");
		}
	}

	public KRunState getState(int stateNum) {
		KRunState state = states.get(stateNum);
		if (state == null) throw new IllegalArgumentException("Selected state does not exist in the graph.");
		return state;
	}

	private void steppingLoop(Integer steps) throws Exception {
		if (currentState == null) {
			throw new IllegalStateException("Cannot step without a current state to step from.");
		}
		for (int i = 0; steps == null || i < steps; i++) {
			KRunState nextStep = krun.step(getState(currentState).getRawResult(), 1).getResult();
			if (states.containsValue(nextStep)) {
				int stateId = states.getKey(nextStep);
				if (stateId == currentState) {
					//we've stopped moving, so that means we must have reached a final state
					return;
				}
				// we've reached this state before, so update the current state and proceed to the next step
				currentState = stateId;
				continue;
			}
			nextStep.setStateId(K.stateCounter++);
			putState(nextStep);
			graph.addVertex(nextStep);
			graph.addEdge(Transition.unlabelled(context), getState(currentState), nextStep);
			currentState = nextStep.getStateId();
		}
	}

	public void step(int steps) throws Exception {
		steppingLoop(steps);
	}

	public void resume() throws Exception {
		steppingLoop(null);
	}

	public SearchResults stepAll(int steps) throws Exception {
		if (currentState == null) {
			throw new IllegalStateException("Cannot step without a current state to step from.");
		}
		SearchResults results = krun.search(null, steps, SearchType.PLUS, defaultPattern, getState(currentState).getRawResult(), defaultPatternInfo).getResult();
		for (SearchResult result : results.getSolutions()) {
			KRunState state = result.getState();
			if (states.containsValue(state)) {
				int stateNum = states.getKey(state);
				state.setStateId(stateNum);
			}	
		}
		mergeSearchGraph(results.getGraph());
		currentState = null;
		return results;
	}

	private void mergeSearchGraph(DirectedGraph<KRunState, Transition> graphFragment) {
		for (KRunState state : graphFragment.getVertices()) {
			if (!states.containsValue(state)) {
				putState(state);
				graph.addVertex(state);
			}
		}
		for (Transition edge : graphFragment.getEdges()) {
			Pair<KRunState> vertices = graphFragment.getEndpoints(edge);
			Transition existingEdge = graph.findEdge(vertices.getFirst(), vertices.getSecond());
			KRunState first = canonicalizeState(vertices.getFirst());
			KRunState second = canonicalizeState(vertices.getSecond());
			if (existingEdge != null && existingEdge.getType() == TransitionType.UNLABELLED) {
				graph.removeEdge(existingEdge);
				graph.addEdge(edge, first, second);
			} else if (existingEdge == null) {
				graph.addEdge(edge, first, second);
			}
		}		
	}

	private KRunState canonicalizeState(KRunState state) {
		int stateNum = states.getKey(state);
		return states.get(stateNum);
	}

	public String printState(int stateNum) {
		KRunState state = getState(stateNum);
		UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
		state.getResult().accept(unparser);
		return state.toString() + ":\n" + unparser.getResult();
	}

	public Transition getEdge(int state1, int state2) {
		KRunState first = getState(state1);
		KRunState second = getState(state2);
		Transition edge = graph.findEdge(first, second);
		if (edge == null) throw new IllegalArgumentException("Edge between states " + state1 + " and " + state2 + " does not exist");
		return edge;
	}

	public String printEdge(int state1, int state2) {
		Transition edge = getEdge(state1, state2);
		String rule;
		if (edge.getType() == TransitionType.RULE) {
			UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
			edge.getRule().accept(unparser);
			rule = unparser.getResult();
		} else if (edge.getType() == TransitionType.LABEL) {
			rule = "rule [" + edge.getLabel() + "]: ...";
		} else {
			rule = "rule ...";
		}
		
		return rule + "\n" + printState(state1) + "\n=>\n" + printState(state2);
	}

	public void readFromStdin(String s) {
		if (currentState == null) {
			throw new IllegalStateException("Wrong command: If you previously used the step-all " +
				"command you must select\nfirst a solution with the select command before " +
				"executing a read from stdin.");
		}
		Term configuration = getState(currentState).getRawResult();
		AppendToStdin transformer = new AppendToStdin(s, context);
		Term result;
		try {
			result = (Term)configuration.accept(transformer);
		} catch (TransformerException e) {
			assert false;
			result = null; //for static purposes
		}
		if (!transformer.getSucceeded()) {
			throw new IllegalStateException("Cannot perform command: Configuration does not " + 
				"have an stdin buffer");
		}
		KRunState newState = new KRunState(result, context);
		if (states.containsValue(newState)) {
			KRunState canonicalNewState = canonicalizeState(newState);
			Transition edge = graph.findEdge(getState(currentState), canonicalNewState);
			if (edge == null) {
				graph.addEdge(Transition.stdin(s, context), 
					getState(currentState), canonicalNewState);
			}
			currentState = canonicalNewState.getStateId();
			return;
		}
		newState.setStateId(K.stateCounter++);
		putState(newState);
		graph.addVertex(newState);
		graph.addEdge(Transition.stdin(s, context), 
			getState(currentState), newState);
		currentState = newState.getStateId();
	}

	private static class AppendToStdin extends CopyOnWriteTransformer {
		private String str;
		private boolean succeeded;
		private boolean inStdin, inBuffer;
		public AppendToStdin(String str, Context context) {
			super("Append a string to the stdin buffer", context);
			this.str = str;
			succeeded = false;
			inStdin = false;
			inBuffer = false;
		}

		public boolean getSucceeded() {
			return succeeded;
		}

		@Override
		public ASTNode transform(Cell cell) throws TransformerException {
			if ("stdin".equals(context.cells.get(cell.getLabel())
				.getCellAttributes().get("stream"))) {
				inStdin = true;
				ASTNode result = super.transform(cell);
				inStdin = false;
				return result;
			}
			return super.transform(cell);
		}

		@Override
		public ASTNode transform(KApp kapp) throws TransformerException {
            if (kapp.getLabel().equals(KLabelConstant.of("#buffer", context))) {
				inBuffer = true;
				ASTNode result = super.transform(kapp);
				inBuffer = false;
				return result;
			}
			return super.transform(kapp);
		}

		@Override
		public ASTNode transform(StringBuiltin s) throws TransformerException {
			if (inStdin && inBuffer) {
				succeeded = true;
				return StringBuiltin.of(s.stringValue() + str);
			}
			return super.transform(s);
		}
	}
}

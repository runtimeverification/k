package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.util.Pair;
import org.apache.commons.collections15.BidiMap;
import org.apache.commons.collections15.bidimap.DualHashBidiMap;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.krun.K;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.Transition.TransitionType;
import org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor;
import org.kframework.utils.DefinitionLoader;
import org.kframework.utils.general.GlobalSettings;

import java.util.Set;

public class KRunApiDebugger implements KRunDebugger {
	private KRun krun;
	private Integer currentState;
	private DirectedGraph<KRunState, Transition> graph;
	private BidiMap<Integer, KRunState> states;

	private static Rule defaultPattern;
	private static Set<String> defaultVars;
	private static RuleCompilerSteps defaultPatternInfo;

	static {
		try { 
			org.kframework.parser.concrete.KParser.ImportTbl(K.compiled_def + "/def/Concrete.tbl");
			ASTNode pattern = DefinitionLoader.parsePattern(K.pattern, "Command line pattern");
			CollectVariablesVisitor vars = new CollectVariablesVisitor();
			pattern.accept(vars);
			defaultVars = vars.getVars().keySet();
			defaultPatternInfo = new RuleCompilerSteps(K.definition);
			pattern = defaultPatternInfo.compile((Rule) pattern, null);

			defaultPattern = (Rule) pattern;
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	

	public KRunApiDebugger(KRun krun, Term cfg) throws KRunExecutionException {
		this.krun = krun;
		KRunState initialState = new KRunState(cfg, K.stateCounter++);
		graph = new DirectedSparseGraph<KRunState, Transition>();
		graph.addVertex(initialState);
		states = new DualHashBidiMap<Integer, KRunState>();
		putState(initialState);
		KRunState reduced = krun.step(cfg, 0).getResult();
		reduced.setStateId(K.stateCounter++);
		putState(reduced);
		graph.addVertex(reduced);
		graph.addEdge(new Transition(TransitionType.REDUCE), initialState, reduced);
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
			graph.addEdge(new Transition(TransitionType.UNLABELLED), getState(currentState), nextStep);
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
		UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens);
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
			UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens);
			edge.getRule().accept(unparser);
			rule = unparser.getResult();
		} else if (edge.getType() == TransitionType.LABEL) {
			rule = "rule [" + edge.getLabel() + "]: ...";
		} else {
			rule = "rule ...";
		}
		
		return rule + "\n" + printState(state1) + "\n=>\n" + printState(state2);
	}
}

package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;

public interface KRunDebugger {
	public DirectedGraph<KRunState, Transition> getGraph();
	public Integer getCurrentState();
	public void setCurrentState(Integer stateNum);
	public KRunState getState(int stateNum);
	public Transition getEdge(int state1, int state2);
	public void step(int steps) throws Exception;
	public SearchResults stepAll(int steps) throws Exception;
	public void resume() throws Exception;
	public String printState(int stateNum);
	public String printEdge(int state1, int state2);
}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.krun.KRunExecutionException;

import edu.uci.ics.jung.graph.DirectedGraph;

/**
The interface to the debugger api of KRun. Each backend can choose to implement this interface any
way it chooses, or it can implement the interface using the {@link KRunApiDebugger} class, which
implements its functionality by relying on calls to the underlying {@link KRun} object.
*/
public interface KRunDebugger {
    /**
    Get the current graph of the explored state space in the transition system.
    @return A graph whose nodes and edges describe the explored state of the program.
    */
    public DirectedGraph<KRunState, Transition> getGraph();

    /**
    Get the state number of the currently selected state.
    @return An unique integer identifying the currently selected state; null if no state is selected
    */
    public Integer getCurrentState();

    /**
    Set the selected state of the debugger.
    @param stateNum An integer uniquely identifying the state to select; null to deselect current
    state.
    @exception IllegalArgumentException Thrown if the specified state is not a valid state in the
    graph (or null)
    */
    public void setCurrentState(Integer stateNum);

    /**
    Get a state by its state number.
    @param stateNum An integer uniquely identifying the state to select
    @return The node in the explored state graph with the specified state number.
    @exception IllegalArgumentException Thrown if the state number is not in the graph
    */
    public KRunState getState(int stateNum);

    /**
    Get the edge connecting two states.
    @param state1 The integral state number of the origin state of the edge.
    @param state2 The integral state number of the destination state of the edge.
    @exception IllegalArgumentException Thrown if no edge connects state1 and state2
    @return Information concerning the transition in the transition system which connected state1 to
    state2
    */
    public Transition getEdge(int state1, int state2);

    /**
    Step a particular number of transitions. This function returns when the specified number of
    steps have been taken, or when rewriting has terminated.
    @param steps The maximum number of transitions to follow through (0 to stop before first
    transition)
    */
    public void step(int steps) throws KRunExecutionException;

    /**
    Explore the complete search graph from the currently selected state forward a specified number
    of steps.
    @param steps The maximum depth of the search to perform.
    @return A set of all new states discovered by the stepper after searching the specified number
    of steps.
    */
    public SearchResults stepAll(int steps) throws KRunExecutionException;

    /**
    Explore the search graph one step at a time until rewriting terminates.
    */
    public void resume() throws KRunExecutionException;
    /**
    Display a textual representation of the specified state.
    @param stateNum The integral state number of the state to print
    @return A textual representation of the state which contains its state number and underlying
    configuration term.
    */
    public String printState(int stateNum);

    /**
    Display a textual representation of the specified edge.
    @param state1 The state number of the origin state of the edge.
    @param state2 The state number of the destination state of the edge.
    @return A textual representation of the edge connecting state1 and state2, containing any
    information the debugger knows about the transition.
    */
    public String printEdge(int state1, int state2);

    /**
    Read a string and append it to the buffer for stdin.
    @param s The string to append to stdin.
    */
    public void readFromStdin(String s);
}

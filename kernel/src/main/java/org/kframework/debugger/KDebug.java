// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.krun.tools.Debugger;

import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The Debugger Interface, represents the
 * Debugger Api. Any Interaction to the Debugger
 * happens through the methods described in this
 * interface.
 */
public interface KDebug {

    /**
     * Change the Checkpoint Interval in the Debugger.
     * Global Setting, will persist across states.
     */
    public void setCheckpointInterval(int interval);

    /**
     * Take a certain number of steps from the current state.
     *
     * @param initialState The StateId of the state to begin taking steps from. Steps are always taken from the last encountered configuration.
     * @param steps        The number of steps to take
     * @return DebuggerState The new state arrived upon.
     * after the operation.
     */
    public DebuggerState step(int initialState, int steps);

    /**
     * Take specified number of steps backwards from current state.
     *
     * @param steps The number of steps to go back.
     * @return DebuggerState Oject depicting the state debugger was in
     * after the operation.
     */
    public DebuggerState backStep(int initialState, int steps);

    /**
     * Go to a certain state in your the execution trace.
     *
     * @param stateNum The id of the state you're wanting to go to.
     */
    public DebuggerState jumpTo(int stateNum, int ConfigurationNum);


    /**
     * Perform a search of the model to find ground configurations that match a
     * specified pattern
     *
     * @param startStateId  StateId to begin searching for a state from. If not specified, the default state of the
     *                      the current Debugger instance is used.
     * @param searchPattern Pattern the use wishes to search for.
     * @param depth         Max depth to explore in the model. Empty parameter enables unbounded depth.
     * @param bounds        Max number of solutions to report. Empty parameter means unbounded.
     * @return
     */
    public List<? extends Map<? extends K, ? extends K>> search(Optional<Integer> startStateId, Rule searchPattern, Optional<Integer> depth, Optional<Integer> bounds);

    /**
     * Resume the execution of the program until a final Configuration is reached.
     *
     * @return State showing the final state the Debugger is in.
     */
    public DebuggerState resume();

    /**
     * Return a list of States the Debugger has been in. A State is essentially a path in the execution tree.
     *
     * @return List of State. The last state in the list is the active State.
     */
    public List<DebuggerState> getStates();

    /**
     * Specified a State and a Configuration, makes it the active state with configuration.
     *
     * @param stateNum         The state number
     * @param configurationNum The configuration within the state
     * @return DebuggerState object containing the State of the debugger. Null if operation fails.
     */
    public int setState(int stateNum, Optional<Integer> configurationNum);

    /**
     * Returns the state the activated state the debugger is in at the moment
     *
     * @return The DebuggerState object corresponding to the Active State
     */
    public int getActiveState();

    /**
     * Allows the user to peek at a particular configuration/state, without changing the current state.
     * <p>
     * Return null if configuration not present.
     *
     * @param stateNum         The state to peek at. Empty for current state.
     * @param configurationNum The configuration to peek it. Empty to look at current configuration.
     *                         That is, if called with both empty state and configuration numbers, will
     *                         return the current state.
     * @return
     */
    public DebuggerState peek(Optional<Integer> stateNum, Optional<Integer> configurationNum);


    /**
     * Create a copy of a state, and make debugger aware of the copy.
     * @param stateNum of the state you'd like to copy
     * @return
     */
    public DebuggerState createCopy(int stateNum);

}


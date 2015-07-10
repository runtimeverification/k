// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.definition.Rule;
import org.kframework.kore.K;

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
     * @param steps The number of steps to take
     * @return DebuggerState Oject depicting the state debugger was in
     * after the operation.
     */
    public DebuggerState step(int steps);

    /**
     * Take specified number of steps backwards from current state.
     *
     * @param steps The number of steps to go back.
     * @return DebuggerState Oject depicting the state debugger was in
     * after the operation.
     */
    public DebuggerState backStep(int steps);

    /**
     * Go to a certain state in your the execution trace.
     *
     * @param stateNum The id of the state you're wanting to go to.
     */
    public DebuggerState jumpTo(int stateNum);


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

    public DebuggerState resume();


}

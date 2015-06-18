// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


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
     *
     * @return DebuggerState Oject depicting the state debugger was in
     * after the operation.
     */
    public DebuggerState step(int steps);

    /**
     * Take specified number of steps backwards from current state.
     * @param steps The number of steps to go back.
     *
     * @return DebuggerState Oject depicting the state debugger was in
     * after the operation.
     */
    public DebuggerState backStep(int steps);

    /**
     * Go back from a given number of steps to a predefined position.
     *
     * You can only select a state that you've already encountered
     */
    public DebuggerState select(int stateNum);


}

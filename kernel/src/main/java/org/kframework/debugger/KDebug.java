package org.kframework.debugger;



/**
 * The Debugger Interface, represents the
 * Debugger Api. Any Interaction to the Debugger
 * happens through the methods described in this
 * interface.
 */
public interface KDebug {

    /**
     *  Take a certain number of steps from the current state.
     */
    public int step(int steps);

    /**
     * Go back from a given number of steps to a predefined position
     */
    public int backStep(int steps);




}

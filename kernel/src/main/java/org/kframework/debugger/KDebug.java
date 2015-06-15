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




}

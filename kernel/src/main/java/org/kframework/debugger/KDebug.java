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
    public KDebugOpResult step(int steps);

    /**
     * Change the Checkpoint Interval in the Debugger.
     *
     * Global Setting, will persist across states.
     */
    public void setCheckpointInterval(int interval);

//    /**
//     * Go back from a given number of steps to a predefined position
//     */
//    public int backStep(int steps);




}

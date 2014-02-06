package org.kframework.backend.java.symbolic;

/**
 * @author AndreiS
 */
public abstract class AbstractUnifier implements Unifier {
    	
    /**
     * Fails the unification task.
     * 
     * @throws UnificationFailure
     */
	public void fail() {
		throw UnificationFailure.UNIFICATION_FAILURE;
	}

}
package org.kframework.backend.pdmc.pda.buchi;

/**
 * Interface for an LTL atom evaluator
 * @param <State> represents states in which the atoms should be evaluated.
 *
 * @author TraianSF
 */

public interface Evaluator<State> {
    /**
     * Set the state in which atoms should be evaluated
     * @param state the (current) state of the system
     */
    void setState(State state);

    /**
     * Evaluate atom id in the current state
     * @param id the ltl atom to be evaluated
     * @return whether id holds in the current state or not
     */
    boolean evaluate(Identifier id);
}

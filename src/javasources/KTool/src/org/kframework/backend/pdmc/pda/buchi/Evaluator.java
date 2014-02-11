package org.kframework.backend.pdmc.pda.buchi;

/**
 * @author Traian
 */
public interface Evaluator<State> {
    boolean evaluate(Identifier id);
    void setState(State state);
}

package org.kframework.backend.pdmc.pda.buchi;

/**
 * @author Traian
 */
public interface Evaluator {
    boolean evaluate(Identifier id);
    void setState(Object state);
}

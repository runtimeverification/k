package org.kframework.backend.pdmc.pda.buchi;

/**
 * @author Traian
 */
public class PromelaTransition {

    private final Expression condition;
    private final BuchiState state;

    public PromelaTransition(Expression condition, BuchiState state) {
        this.condition = condition;
        this.state = state;
    }

    public Expression getCondition() {
        return condition;
    }

    public BuchiState getState() {
        return state;
    }

    @Override
    public String toString() {
        return ":: (" + condition + ") -> goto " + state;
    }
}

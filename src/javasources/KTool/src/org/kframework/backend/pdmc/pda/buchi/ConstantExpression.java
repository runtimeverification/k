package org.kframework.backend.pdmc.pda.buchi;

/**
 * @author Traian
 */
public class ConstantExpression extends Expression {
    private final boolean value;

    public ConstantExpression(boolean b) {
        this.value = b;
    }

    @Override
    public String toString() {
        return String.valueOf(value);
    }

    @Override
    public boolean evaluate(Evaluator evaluator) {
        return value;
    }
}

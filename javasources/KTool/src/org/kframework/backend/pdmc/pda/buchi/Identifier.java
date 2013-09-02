package org.kframework.backend.pdmc.pda.buchi;

import org.kframework.backend.pdmc.pda.buchi.parser.Token;

/**
 * @author Traian
 */
public class Identifier extends Expression {

    String name;

    private Identifier(String image) {
        this.name = image;
    }

    public static Identifier of(Token id) {
        return new Identifier(id.image);
    }

    @Override
    public boolean evaluate(Evaluator evaluator) {
        return evaluator.evaluate(this);
    }

    @Override
    public String toString() {
        return name;
    }
}

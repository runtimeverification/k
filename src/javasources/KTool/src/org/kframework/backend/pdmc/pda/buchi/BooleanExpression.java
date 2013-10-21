package org.kframework.backend.pdmc.pda.buchi;

import org.kframework.backend.pdmc.pda.buchi.parser.PromelaBuchiParserConstants;

/**
 * @author Traian
 */
public class BooleanExpression extends Expression implements PromelaBuchiParserConstants {
    private final Expression rand1;

    @Override
    public String toString() {
        switch (opCode) {
            case LNOT:
                return "!" + rand1.toString();
            case LAND:
                return rand1.toString() + " && " + rand2.toString();
            case LOR:
                return rand1.toString() + " || " + rand2.toString();
        }
        return super.toString();
    }

    private final Expression rand2;
    private final int opCode;

    public BooleanExpression(int opCode, Expression rand1) {
        this(opCode, rand1, null);
    }

    public BooleanExpression(int opCode, Expression rand1, Expression rand2) {
        this.rand1 = rand1;
        this.rand2 = rand2;
        this.opCode = opCode;
    }

    @Override
    public boolean evaluate(Evaluator evaluator) {
        switch (opCode) {
            case LNOT:
                return !rand1.evaluate(evaluator);
            case LAND:
                return rand1.evaluate(evaluator) && rand2.evaluate(evaluator);
            case LOR:
                return rand1.evaluate(evaluator) || rand2.evaluate(evaluator);
        }
        assert false : "Unsupported operation";
        return false;
    }
}

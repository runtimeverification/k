// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.jfkbits;

public class LispParser {
    LispTokenizer tokenizer;

    public LispParser(LispTokenizer input) {
        tokenizer = input;
    }

    public class ParseException extends Exception {

        /**
         *
         */
        private static final long serialVersionUID = 1L;

    }

    public interface Expr {
        public String getKIF();
    }

    public Expr parseExpr() throws ParseException {
        Token token = tokenizer.next();
        switch (token.type) {
        case '(':
            return parseExprList(token);
        case '"':
            return new StringAtom(token.text);
        default:
            return new Atom(token.text);
        }
    }

    protected ExprList parseExprList(Token openParen) throws ParseException {
        ExprList acc = new ExprList();
        while (tokenizer.peekToken().type != ')') {
            Expr element = parseExpr();
            acc.add(element);
        }
        @SuppressWarnings("unused")
        Token closeParen = tokenizer.next();
        return acc;
    }

}

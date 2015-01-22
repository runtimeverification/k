// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/**
 * Applications that are not in sort K, or have not yet been flattened.
 */
public class ParseError extends ASTNode {
    /** A unique identifier corresponding to a production, matching the SDF cons */
    String message = null;

    public ParseError(ParseError node) {
        super(node);
        this.message = node.message;
    }

    @Override
    public String toString() {
        return "Parse error: " + message;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof ParseError))
            return false;
        ParseError tc = (ParseError) obj;

        return tc.message.equals(this.message);
    }

    @Override
    public int hashCode() {
        return message.hashCode();
    }

    @Override
    public ParseError shallowCopy() {
        return new ParseError(this);
    }

    public String getMessage() {
        return message;
    }

    public void setMessage(String message) {
        this.message = message;
    }
}

package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/17/13
 * Time: 12:54 PM
 * To change this template use File | Settings | File Templates.
 */
public abstract class Collection extends Term {
    /**
     * Implements a specialized Visitor pattern.
     * Here the matcher will accept a term, rather than operating only on
     * the this pointer, as would a normal Visitor
     *
     * @param this    - is the pattern to be matched
     * @param toMatch is the term we are attempting to match against
     */
    @Override
    public void accept(Matcher matcher, org.kframework.kil.Term toMatch) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer visitor) throws TransformerException {
        throw new UnsupportedOperationException();
    }

    /**
     * Implements a Visitor pattern.
     *
     * @param visitor
     */
    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }
}

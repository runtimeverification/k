package org.kframework.backend.java.kil;

import org.kframework.kil.ASTNode;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Root of the Java Rewrite Engine internal representation class hierarchy.
 *
 * @author: AndreiS
 */
public abstract class JavaSymbolicObject extends ASTNode {



    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }
}

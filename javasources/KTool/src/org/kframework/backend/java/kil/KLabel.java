package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * A KLabel.
 *
 * @author AndreiS
 */
public abstract class KLabel extends Term {

    protected KLabel() {
        super(Kind.KLABEL);
    }

    @Override
    public boolean isSymbolic() {
        /* AndreiS: no support for symbolic KLabels */
        return false;
    }

    public abstract boolean isConstructor();

    public abstract boolean isFunction();

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

}

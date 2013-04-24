package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/17/13
 * Time: 12:54 PM
 * To change this template use File | Settings | File Templates.
 */
public abstract class Collection extends Term {

    protected final Variable frame;

    protected Collection(Variable frame, String kind) {
        super(kind);

        assert frame == null || frame.getKind().equals(kind)
                : "unexpected sort " + frame.getKind() + " for frame variable " + frame.getName()
                + "; expected sort " + kind;

        this.frame = frame;
    }

    public boolean hasFrame() {
        return frame != null;
    }

    public Variable getFrame() {
        assert hasFrame();

        return frame;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

}

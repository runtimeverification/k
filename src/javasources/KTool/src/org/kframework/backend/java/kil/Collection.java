package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.List;


/**
 *
 * @author AndreiS
 */
public abstract class Collection extends Term {

    protected final Variable frame;

    public List<Term> getContents() {
        return contents;
    }

    public void setContents(List<Term> contents) {
        this.contents = contents;
    }

    protected java.util.List<Term> contents;

    protected Collection(Variable frame, Kind kind) {
        super(kind);

        assert frame == null || frame.kind() == kind
                : "unexpected kind " + frame.kind() + " for frame variable " + frame.name()
                + "; expected kind " + kind;

        this.frame = frame;
        this.contents = new ArrayList<Term>();
    }

    public boolean hasFrame() {
        return frame != null;
    }

    public Variable frame() {
        assert hasFrame();

        return frame;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Collection)) {
            return false;
        }

        Collection collection = (Collection) object;
        return frame == null ? collection.frame == null : frame.equals(collection.frame);
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

package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


/**
 * A collection of {@link Term}s.
 * 
 * @author AndreiS
 */
@SuppressWarnings("serial")
public abstract class Collection extends Term {

    /**
     * Represents the rest part of this {@code Collection} which is not
     * explicitly specified (that is, simply being referred as a variable in
     * whole).
     */
    protected final Variable frame;

    /**
     * Creates an instance of class {@code Collection} given its kind and a
     * frame variable. If the given frame is non-null, the kind of the frame
     * must be equal to the kind of the instance.
     * 
     * @param frame
     *            the frame variable
     * @param kind
     *            the kind
     */
    protected Collection(Variable frame, Kind kind) {
        super(kind);

        assert frame == null || frame.kind() == kind
                : "unexpected kind " + frame.kind() + " for frame variable " + frame.name()
                + "; expected kind " + kind;

        this.frame = frame;
    }

    /**
     * Checks if this {@code Collection} contains a frame variable.
     */
    public boolean hasFrame() {
        return frame != null;
    }

    /**
     * @return the frame variable of this {@code Collection} if there is one;
     *         otherwise, fail the assertion
     */
    public Variable frame() {
        assert hasFrame();

        return frame;
    }

    /**
     * Returns true if this {@code Collection} does not have any contents and does not have a frame.
     */
    public boolean isEmpty() {
        return size() == 0 && !hasFrame();
    }

    /**
     * Returns the size of the contents of this {@code Collection}.
     *
     * @return the size of the contents
     */
    public abstract int size();

    @Override
    public boolean isSymbolic() {
        return false;
    }
    
    @Override
    public int hashCode() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object) {
        throw new UnsupportedOperationException();
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

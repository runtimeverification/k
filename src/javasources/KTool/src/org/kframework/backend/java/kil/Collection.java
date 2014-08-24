// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


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
     * Returns true if this {@code Collection} does not contain any content.
     */
    public boolean isEmpty() {
        return size() == 0 && isConcreteCollection();
    }

    /**
     * Returns the size of the contents of this {@code Collection}.
     *
     * TODO(YilongL): rename to concreteSize?
     *
     * @return the size of the contents
     */
    public abstract int size();

    /**
     * Returns true if this collection contains elements or entries, but does not contain patterns,
     * functions or variables.
     */
    public abstract boolean isConcreteCollection();

    /**
     * Checks if this {@code Collection} term is a proper left-hand side view.
     *
     * @return {@code true} if this {@code Collection} term can be used as a
     *         pattern on the left-hand side of a rule; otherwise, {@code false}
     */
    public abstract boolean isLHSView();

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

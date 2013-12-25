package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
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
     * Represents the elements of this {@code Collection} that are explicitly
     * specified. These elements are stored as a list of {@code Term}s.
     */
    protected java.util.List<Term> contents;

    /**
     * Represents the rest part of this {@code Collection} which is not
     * explicitly specified (that is, simply being referred as a variable in
     * whole).
     */
    protected final Variable frame;

    /**
     * @see {@link Collection#contents}
     * @return an unmodifiable view of the explicitly specified elements in this
     *         {@code Collection}
     */
    public List<Term> getContents() {
        return Collections.unmodifiableList(contents);
    }

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
        this.contents = new ArrayList<Term>();
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
        // TODO(YilongL): why not take into consideration Collection#contents?
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

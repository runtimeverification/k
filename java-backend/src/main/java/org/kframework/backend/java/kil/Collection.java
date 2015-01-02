// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;

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
     * Returns a KORE (KLabel/KList) representation of this collection. The returned representation
     * is not unique (due to associativity/commutativity).
     * {@link org.kframework.backend.java.kil.Term#evaluate} is the inverse operation.
     */
    public Term toK(TermContext context) {
        DataStructureSort sort = context.definition().context().dataStructureSortOf(
                sort().toFrontEnd());
        List<Term> components = getKComponents(context);

        if (components.isEmpty()) {
            return KItem.of(
                    KLabelConstant.of(sort.unitLabel(), context.definition().context()),
                    KList.EMPTY,
                    context);
        }

        Term result = components.get(components.size() - 1);
        for (int i = components.size() - 2; i >= 0; --i) {
            Term component = components.get(i);
            result = KItem.of(
                    KLabelConstant.of(sort.constructorLabel(), context.definition().context()),
                    KList.concatenate(component, result),
                    context, component.getSource(), component.getLocation());
        }
        return result;
    }

    /**
     * Returns a list aggregating the base terms and the elements/entries of this collection.
     * Each collection is responsible for representing its elements/entries in KLabel and KList
     * format.
     */
    abstract protected List<Term> getKComponents(TermContext context);

    /**
     * Checks if this {@code Collection} contains a frame variable.
     */
    public final boolean hasFrame() {
        return frame != null;
    }

    /**
     * @return the frame variable of this {@code Collection} if there is one;
     *         otherwise, fail the assertion
     */
    public final Variable frame() {
        assert hasFrame();

        return frame;
    }

    public abstract java.util.Collection<Variable> collectionVariables();

    /**
     * Returns true if this {@code Collection} does not contain any content.
     */
    public boolean isEmpty() {
        return concreteSize() == 0 && isConcreteCollection();
    }

    /**
     * Returns the number of elements or entries of this {@code Collection}.
     */
    public abstract int concreteSize();

    /**
     * Returns true if this collection contains elements or entries, but does not contain patterns,
     * functions or variables.
     */
    public abstract boolean isConcreteCollection();

    @Override
    public final boolean isSymbolic() {
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

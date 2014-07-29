// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;


/**
 * Represents a K cell term in the Java backend. Since cells can be nested, the
 * content of a cell is either a collection of cells (i.e., a
 * {@link CellCollection}) or a non-cell K term.
 * <p>
 * In contrast to its generic KIL counterpart, the multiplicity information is
 * stored in the {@code CellCollection} that contains this cell.
 *
 * @see org.kframework.kil.Cell
 *
 * @author AndreiS
 */
@SuppressWarnings("serial")
public class Cell<T extends Term> extends Term {

    private final String label;
    private final Kind contentKind;
    private T content;

    public Cell(String label, T content) {
        super(Kind.CELL);

        assert content.kind() == Kind.CELL_COLLECTION
                || content.kind == Kind.CELL
                || content.kind() == Kind.K
                || content.kind() == Kind.KITEM
                || content.kind() == Kind.KLABEL
                || content.kind() == Kind.KLIST:
                //|| content.kind() == Kind.MAP:
                "unexpected cell kind " + content.kind();
        this.label = label;
        this.contentKind = content.kind();
        this.content = content;
    }

    public String getLabel() {
        return label;
    }

    public Kind contentKind() {
        return contentKind;
    }

    public T getContent() {
        return content;
    }

    /**
     * TODO(DwightG): Fix this with dependency injection
     * <p>
     * Unsafe operation to set the content of the {@code Cell}; this method
     * violates the immutability contract on {@code Term} and its subclasses.
     * This method is only used in the {@link KAbstractRewriteMachine} to allow
     * efficient in-place rewriting; as a result, it is the caller's
     * responsibility to make defensive copy before calling this operation to
     * avoid modifying shared {@code Cell}s. Besides, this operation should be
     * used together with some mechanism to properly invalidates the cached
     * hashCode of all the affected {@code Term}s.
     *
     * @param content the new content
     */
    public void unsafeSetContent(T content) {
        this.content = content;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public Sort sort() {
        return kind.asSort();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Cell)) {
            return false;
        }

        Cell<?> cell = (Cell<?>) object;
        return label.equals(cell.label) && content.equals(cell.content);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + label.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + content.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeHasCell() {
        return true;
    }

    @Override
    public String toString() {
        return "<" + label + ">" + content + "</" + label + ">";
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

//    @Override
//    public String sort() {
//        return KSorts.BAG_ITEM;
//    }

}

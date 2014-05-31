// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.KSorts;


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
    private final T content;

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

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public String sort() {
        return kind.toString();
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
    public int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + label.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + content.hashCode();
        return hashCode;
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

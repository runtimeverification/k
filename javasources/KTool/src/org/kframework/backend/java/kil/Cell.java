package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 *
 *
 * @author AndreiS
 */
public class Cell<T extends Term> extends Term {

    private final String label;
    private final Kind contentKind;
    private final T content;

    public Cell(String label, T content) {
        super(Kind.CELL);

        assert content.kind() == Kind.CELL_COLLECTION
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

    public Kind getContentKind() {
        return contentKind;
    }

    public T getContent() {
        return content;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public String toString() {
        return "<" + label + ">" + content + "</" + label + ">";
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
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

package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
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

        assert content.getKind() == Kind.CELL_COLLECTION
                || content.getKind() == Kind.K
                || content.getKind() == Kind.KITEM
                || content.getKind() == Kind.KLABEL
                || content.getKind() == Kind.KLIST
                || content.getKind() == Kind.MAP:
                "unexpected cell kind " + content.getKind();
        this.label = label;
        this.contentKind = content.getKind();
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
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
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

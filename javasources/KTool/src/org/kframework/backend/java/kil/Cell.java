package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/20/13
 * Time: 6:52 PM
 * To change this template use File | Settings | File Templates.
 */
public class Cell<T extends Term> extends Term {

    private final String label;
    private final String contentKind;
    private final T content;

    public Cell(String label, T content) {
        super("Cell");

        assert content.getKind().equals("K")
                || content.getKind().equals("KSequence")
                || content.getKind().equals("Map")
                || content.getKind().equals("CellCollection");
        this.label = label;
        this.contentKind = content.getKind();
        this.content = content;
    }

    public String getLabel() {
        return label;
    }

    public String getContentKind() {
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

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
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

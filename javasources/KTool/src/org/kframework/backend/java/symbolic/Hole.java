package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/28/13
 * Time: 1:52 PM
 * To change this template use File | Settings | File Templates.
 */
public class Hole extends Term {

    public static final Hole HOLE = new Hole();

    private Hole() {
        super("K");
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public String toString() {
        return "HOLE";
    }

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

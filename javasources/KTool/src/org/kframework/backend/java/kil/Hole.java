package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * A hole (a term of the form "HOLE").
 *
 * @author AndreiS
 */
public class Hole extends Term {

    public static final Hole HOLE = new Hole();

    private Hole() {
        super(Kind.KITEM);
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

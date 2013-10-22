package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import com.microsoft.z3.Expr;


/**
 * @author: AndreiS
 */
public class Z3Term extends Term {

    private final Expr expression;

    public Z3Term(Expr expression) {
        super(Kind.KITEM);
        this.expression = expression;
    }

    public Expr expression() {
        return expression;
    }

    @Override
    public boolean isSymbolic() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 1:50 PM
 * To change this template use File | Settings | File Templates.
 */
public class InjectionKLabel extends KLabel {

    private final Term term;

    InjectionKLabel(Term term) {
        this.term = term;
    }

    public Term getTerm() {
        return term;
    }

    @Override
    public boolean isConstructor() {
        return false;
    }

    @Override
    public boolean isFunction() {
        return false;
    }

    @Override
    public String toString() {
        return "# " + term;
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

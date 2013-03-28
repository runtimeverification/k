package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 4:57 PM
 * To change this template use File | Settings | File Templates.
 */
public class BuiltinConstant extends Term {

    private final String value;
    private final String sort;

    public BuiltinConstant(String value, String sort) {
        super("BuiltinConstant");

        this.value = value;
        this.sort = sort;
    }

    public String getValue() {
        return value;
    }

    public String getSort() {
        return sort;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public String toString() {
        return value + "." + sort;
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

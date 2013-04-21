package org.kframework.kil;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 4/16/13
 * Time: 4:49 PM
 * To change this template use File | Settings | File Templates.
 */
public abstract class Builtin extends Term {

    protected Builtin(String sort) {
        super(sort);
    }

    protected Builtin(Element element) {
        super(element);
    }

    public abstract String getValue();

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

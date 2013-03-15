package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/8/13
 * Time: 3:08 PM
 * To change this template use File | Settings | File Templates.
 */
public class UnnamedVariable extends Variable {

    static private int counter = 0;
    final private int id;

    private UnnamedVariable(String sort, int id) {
        super("", sort);
        this.id = id;
    }

    public static UnnamedVariable getFreshVariable(String sort) {
        return new UnnamedVariable(sort, counter++);
    }

    public int getId() {
        return id;
    }

    public String toString() {
        return "__var_" + id + ":" + sort + " ";
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer visitor) throws TransformerException {
        return visitor.transform(this);
    }

    @Override
    public void accept(Matcher matcher, Term toMatch){
        matcher.match(this, toMatch);
    }

    @Override
    public boolean equals(Object object) {
        if (object instanceof UnnamedVariable) {
            UnnamedVariable variable = (UnnamedVariable) object;
            return sort.equals(variable.getSort()) && id == variable.getId();
        }

        return false;
    }

    @Override
    public int hashCode() {
        return sort.hashCode() + Integer.valueOf(id).hashCode();
    }

    @Override
    public Variable shallowCopy() {
        return new Variable(this);
    }
}

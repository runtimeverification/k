package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Sorted;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 12:49 PM
 * To change this template use File | Settings | File Templates.
 */
public class Variable extends Term implements Sorted {

    protected final String name;
    protected final String sort;

    public Variable(String name, String sort) {
        super(Utils.sortToKind(sort));

        this.name = name;
        this.sort = sort;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    public String getName() {
        return name;
    }

    /**
     * @return the string representation of the sort of this variable.
     */
    @Override
    public String getSort() {
        return sort;
    }

	@Override
	public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Variable)) {
            return false;
        }

        Variable variable = (Variable) object;
        return name.equals(variable.name) && sort.equals(variable.sort);
	}

	@Override
	public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + name.hashCode();
        hash = hash * Utils.HASH_PRIME + sort.hashCode();
		return hash;
	}

    @Override
    public String toString() {
        return name + ":" + sort;
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

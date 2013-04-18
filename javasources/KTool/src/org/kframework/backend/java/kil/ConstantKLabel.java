package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 1:50 PM
 * To change this template use File | Settings | File Templates.
 */
public class ConstantKLabel extends KLabel {

    private final String label;
    private final boolean isFunction;

    public ConstantKLabel(String label) {
        this.label = label;

        boolean isFunction = false;
        for (Production production : Utils.productionsOf(label)) {
            if (production.containsAttribute(Attribute.FUNCTION.getKey())) {
                isFunction = true;
                break;
            }
            if (production.containsAttribute(Attribute.PREDICATE.getKey())) {
                isFunction = false;
                break;
            }
        }
        this.isFunction = isFunction;
    }

    public String getLabel() {
        return label;
    }

    @Override
    public boolean isConstructor() {
        return !isFunction;
    }

    @Override
    public boolean isFunction() {
        return isFunction;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ConstantKLabel)) {
            return false;
        }

        ConstantKLabel constantKLabel = (ConstantKLabel) object;
        return label.equals(constantKLabel.getLabel());
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + label.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return label;
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

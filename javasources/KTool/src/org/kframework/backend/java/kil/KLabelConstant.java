package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 1:50 PM
 * To change this template use File | Settings | File Templates.
 */
public class KLabelConstant extends KLabel {

    private final String label;
    private final boolean isFunction;

    public KLabelConstant(String label, Context context) {
        this.label = label;

        boolean isFunction = false;
        for (Production production : productionsOf(context)) {
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

    public List<Production> productionsOf(Context context) {
        Set<String> conses = context.labels.get(label);
        if (conses == null) {
            return Collections.<Production>emptyList();
        }

        ArrayList<Production> productions = new ArrayList<Production>();
        for (String cons : conses) {
            assert context.conses.containsKey(cons);

            productions.add(context.conses.get(cons));
        }

        return productions;
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

        if (!(object instanceof KLabelConstant)) {
            return false;
        }

        KLabelConstant kLabelConstant = (KLabelConstant) object;
        return label.equals(kLabelConstant.getLabel());
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

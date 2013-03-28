package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.loader.DefinitionHelper;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 1:50 PM
 * To change this template use File | Settings | File Templates.
 */
public class ConstantKLabel extends KLabel {

    private final String label;

    public ConstantKLabel(String label) {
        this.label = label;
    }

    public String getLabel() {
        return label;
    }

    @Override
    public boolean isConstructor() {
        return !isFunction();
    }

    @Override
    public boolean isFunction() {
        if (!DefinitionHelper.labels.containsKey(label)) {
            return false;
        }

        for (String cons : DefinitionHelper.labels.get(label)) {
            assert DefinitionHelper.conses.containsKey(cons);

            Production production = DefinitionHelper.conses.get(cons);
            if (production.containsAttribute(Attribute.FUNCTION.getKey())) {
                return true;
            }
            if (production.containsAttribute(Attribute.PREDICATE.getKey())) {
                return true;
            }
        }

        return false;
    }

    @Override
    public boolean equals(Object object) {
        if (!(object instanceof ConstantKLabel)) {
            return false;
        }

        ConstantKLabel constantKLabel = (ConstantKLabel) object;
        return label.equals(constantKLabel.getLabel());
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

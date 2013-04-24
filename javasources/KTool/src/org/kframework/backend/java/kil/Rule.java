package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.VariableVisitor;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;


import java.util.Set;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/25/13
 * Time: 12:10 PM
 * To change this template use File | Settings | File Templates.
 */
public class Rule extends ASTNode implements Transformable, Visitable {

    private final Term condition;
    private final Term leftHandSide;
    private final Term rightHandSide;


    public Rule(Term leftHandSide, Term rightHandSide, Term condition, Attributes attributes) {
        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.condition = condition;
        super.setAttributes(attributes);
    }

    public Rule(Term leftHandSide, Term rightHandSide, Term condition) {
        this(leftHandSide, rightHandSide, condition, null);
    }

    public Rule(Term leftHandSide, Term rightHandSide, Attributes attributes) {
        this(leftHandSide, rightHandSide, null, attributes);
    }

    public Rule(Term leftHandSide, Term rightHandSide) {
        this(leftHandSide, rightHandSide, null, null);
    }

    public Term getCondition() {
        assert hasCondition();

        return condition;
    }

    public Term getLeftHandSide() {
        return leftHandSide;
    }

    public Term getRightHandSide() {
        return rightHandSide;
    }

    public boolean hasCondition() {
        return condition != null;
    }

    @Override
    public String toString() {
        String string = "rule " + leftHandSide + " => " + rightHandSide;
        if (condition != null) {
            string += " when " + condition;
        }
        return string;
    }

    public Set<Variable> variableSet() {
        VariableVisitor visitor = new VariableVisitor();
        accept(visitor);
        return visitor.getVariableSet();
    }

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(org.kframework.kil.visitors.Transformer transformer)
            throws org.kframework.kil.visitors.exceptions.TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(org.kframework.kil.visitors.Visitor visitor) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

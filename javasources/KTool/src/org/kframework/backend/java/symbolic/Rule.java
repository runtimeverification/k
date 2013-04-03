package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/25/13
 * Time: 12:10 PM
 * To change this template use File | Settings | File Templates.
 */
public class Rule extends ASTNode {

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

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public ASTNode accept(Transformer visitor) throws TransformerException {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

}

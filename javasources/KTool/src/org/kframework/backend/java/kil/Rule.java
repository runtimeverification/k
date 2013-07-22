package org.kframework.backend.java.kil;

import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.VariableVisitor;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;

import java.util.Collection;
import java.util.Set;


/**
 * A K rule in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Rule extends ASTNode implements Visitable {

    private final Term leftHandSide;
    private final Term rightHandSide;
    private final Collection<Term> condition;
    private final Collection<Variable> freshVariables;
    private final SymbolicConstraint lookups;
    private final IndexingPair indexingPair;

    public Rule(
            Term leftHandSide,
            Term rightHandSide,
            Collection<Term> condition,
            Collection<Variable> freshVariables,
            SymbolicConstraint lookups,
            IndexingPair indexingPair,
            Attributes attributes) {
        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.condition = condition;
        this.freshVariables = freshVariables;
        this.lookups = lookups;
        this.indexingPair = indexingPair;
        super.setAttributes(attributes);
    }

    /*
    public Rule(Term leftHandSide, Term rightHandSide, Term condition) {
        this(leftHandSide, rightHandSide, condition, null);
    }

    public Rule(Term leftHandSide, Term rightHandSide, Attributes attributes) {
        this(leftHandSide, rightHandSide, null, attributes);
    }

    public Rule(Term leftHandSide, Term rightHandSide) {
        this(leftHandSide, rightHandSide, null, null);
    }
    */

    public Collection<Term> condition() {
        return condition;
    }

    public Collection<Variable> freshVariables() {
        return freshVariables;
    }

    public KLabelConstant functionKLabel() {
        assert attributes.containsAttribute(Attribute.FUNCTION_KEY);

        return (KLabelConstant) ((KItem) leftHandSide).kLabel();
    }

    public IndexingPair indexingPair() {
        return indexingPair;
    }

    public Term leftHandSide() {
        return leftHandSide;
    }

    public SymbolicConstraint lookups() {
        return lookups;
    }

    public Term rightHandSide() {
        return rightHandSide;
    }

    @Override
    public String toString() {
        String string = "rule " + leftHandSide + " => " + rightHandSide;
        if (condition != null) {
            string += " when " + condition;
        }
        if (!lookups.isTrue()) {
            if (condition != null) {
                string += " when ";
            } else {
                string += " " + SymbolicConstraint.SEPARATOR + " ";
            }
            string += lookups;
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
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

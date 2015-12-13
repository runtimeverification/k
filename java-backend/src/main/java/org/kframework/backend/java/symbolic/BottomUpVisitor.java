// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;

import java.util.Map;


/**
 * A bottom-up implementation of the visitor pattern.
 *
 * @author AndreiS
 */
public class BottomUpVisitor implements Visitor {

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public void visit(BitVector bitVector) {
        visit((Token) bitVector);
    }

    @Override
    public void visit(BoolToken boolToken) {
        visit((Token) boolToken);
    }

    @Override
    public void visit(BuiltinList node) {
        for (Term t : node.elementsLeft()) t.accept(this);
        for (Term t : node.baseTerms()) t.accept(this);
        for (Term t : node.elementsRight()) t.accept(this);
    }

    @Override
    public void visit(BuiltinMap builtinMap) {
        for (java.util.Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
            entry.getKey().accept(this);
            entry.getValue().accept(this);
        }
        for (Term term : builtinMap.baseTerms()) {
            term.accept(this);
        }
        visit((Collection) builtinMap);
    }

    @Override
    public void visit(BuiltinSet builtinSet) {
        for (Term term : builtinSet.elements()) {
            term.accept(this);
        }
        for (Term term : builtinSet.baseTerms()) {
            term.accept(this);
        }
        visit((Collection) builtinSet);
    }

    @Override
    public void visit(CellCollection cellCollection) {
        for (CellCollection.Cell cell : cellCollection.cells().values()) {
            cell.content().accept(this);
        }
        for (Term term : cellCollection.baseTerms()) {
            term.accept(this);
        }
        visit((Collection) cellCollection);
    }

    @Override
    public void visit(Collection collection) {
        visit((Term) collection);
    }

    @Override
    public void visit(ConstrainedTerm node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void visit(Hole hole) {
        visit((Term) hole);
    }

    @Override
    public void visit(IntToken intToken) {
        visit((Token) intToken);
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        visit((KLabel) kLabelConstant);
    }

    @Override
    public void visit(KLabelFreezer kLabelFreezer) {
        kLabelFreezer.term().accept(this);
        visit((KLabelInjection) kLabelFreezer);
    }

    @Override
    public void visit(KLabelInjection kLabelInjection) {
        kLabelInjection.term().accept(this);
        visit((KLabel) kLabelInjection);
    }

    @Override
    public void visit(KItem kItem) {
        kItem.kLabel().accept(this);
        kItem.kList().accept(this);
        visit((Term) kItem);
    }

    @Override
    public void visit(KItemProjection kItemProjection) {
        kItemProjection.term().accept(this);
        visit((Term) kItemProjection);
    }

    @Override
    public void visit(InjectedKLabel injectedKLabel) {
        injectedKLabel.injectedKLabel().accept(this);
        visit((Term) injectedKLabel);
    }

    @Override
    public void visit(RuleAutomatonDisjunction ruleAutomatonDisjunction) {
        ruleAutomatonDisjunction.disjunctions().stream().forEach(p -> p.getLeft().accept(this));
    }

    @Override
    public void visit(InnerRHSRewrite innerRHSRewrite) { }

    @Override
    public void visit(KCollection kCollection) {
        for (Term term : kCollection) {
            term.accept(this);
        }
        if (kCollection.hasFrame()) {
            kCollection.frame().accept(this);
        }
        visit((Collection) kCollection);
    }

    @Override
    public void visit(KLabel kLabel) {
        visit((Term) kLabel);
    }

    @Override
    public void visit(KList kList) {
        visit((KCollection) kList);
    }

    @Override
    public void visit(KSequence kSequence) {
        visit((KCollection) kSequence);
    }

    @Override
    public void visit(MetaVariable metaVariable) {
        visit((Token) metaVariable);
    }

    @Override
    public void visit(Rule rule) {
        rule.leftHandSide().accept(this);
        rule.rightHandSide().accept(this);
        rule.lookups().accept(this);
        for (Term term : rule.requires()) {
            term.accept(this);
        }
        for (Term term : rule.ensures()) {
            term.accept(this);
        }
        for (Variable variable : rule.freshConstants()) {
            variable.accept(this);
        }
    }

    @Override
    public void visit(ConjunctiveFormula node) {
        for (Map.Entry<Variable, Term> entry : node.substitution().entrySet()) {
            entry.getKey().accept(this);
            entry.getValue().accept(this);
        }
        for (Equality equality : node.equalities()) {
            equality.leftHandSide().accept(this);
            equality.rightHandSide().accept(this);
        }
        for (DisjunctiveFormula disjunctiveFormula : node.disjunctions()) {
            disjunctiveFormula.accept(this);
        }
    }

    @Override
    public void visit(DisjunctiveFormula node) {
        for (ConjunctiveFormula conjunctiveFormula : node.conjunctions()) {
            conjunctiveFormula.accept(this);
        }
    }

    @Override public void visit(Term term) { }

    @Override
    public void visit(Token token) {
        visit((Term) token);
    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        visit((Term) uninterpretedToken);
    }

    @Override
    public void visit(Variable variable) {
        visit((Term) variable);
    }
}

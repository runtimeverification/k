// Copyright (c) 2013-2014 K Team. All Rights Reserved.
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
        if (node.hasFrame()) node.frame().accept(this);
        for (Term t : node.elementsLeft()) t.accept(this);
        for (Term t : node.elementsRight()) t.accept(this);
    }

    @Override
    public void visit(BuiltinMap builtinMap) {
        for (java.util.Map.Entry<Term, Term> entry : builtinMap) {
            entry.getKey().accept(this);
            entry.getValue().accept(this);
        }
        visit((Collection) builtinMap);
    }

    @Override
    public void visit(BuiltinSet builtinSet) {
        for (Term term : builtinSet.elements()) {
            term.accept(this);
        }
//        for (BuiltinSet.Operation operation : builtinSet.operations()) {
//            operation.element().accept(this);
//        }
        visit((Collection) builtinSet);
    }

    @Override
    public void visit(Cell cell) {
        cell.getContent().accept(this);
        visit((Term) cell);
    }

    @Override
    public void visit(CellCollection cellCollection) {
        for (Cell cell : cellCollection.cells()) {
            cell.accept(this);
        }
        for (Variable variable : cellCollection.baseTerms()) {
            variable.accept(this);
        }
        visit((Collection) cellCollection);
    }

    @Override
    public void visit(Collection collection) {
        if (collection.hasFrame()) {
            collection.frame().accept(this);
        }
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
    public void visit(KCollection kCollection) {
        for (Term term : kCollection) {
            term.accept(this);
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
    public void visit(ListLookup listLookup) {
        listLookup.list().accept(this);
        listLookup.key().accept(this);
    }

    @Override
    public void visit(MapKeyChoice mapKeyChoice) {
        mapKeyChoice.map().accept(this);
        visit((Term) mapKeyChoice);
    }

    @Override
    public void visit(MapLookup mapLookup) {
        mapLookup.map().accept(this);
        mapLookup.key().accept(this);
        visit((Term) mapLookup);
    }

    @Override
    public void visit(MapUpdate mapUpdate) {
        mapUpdate.map().accept(this);
        for (Term key : mapUpdate.removeSet()) {
            key.accept(this);
        }
        for (java.util.Map.Entry<Term, Term> entry : mapUpdate.updateMap().entrySet()) {
            entry.getKey().accept(this);
            entry.getValue().accept(this);
        }
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
        for (Variable variable : rule.freshVariables()) {
            variable.accept(this);
        }
    }

    @Override
    public void visit(SetElementChoice setElementChoice) {
        setElementChoice.set().accept(this);
        visit((Term) setElementChoice);
    }

    @Override
    public void visit(SetLookup setLookup) {
        setLookup.base().accept(this);
        setLookup.key().accept(this);
        visit((Term) setLookup);
    }

    @Override
    public void visit(SetUpdate setUpdate) {
        setUpdate.base().accept(this);
        for (Term key : setUpdate.removeSet()) {
            key.accept(this);
        }
    }

    @Override
    public void visit(SymbolicConstraint node) {
        for (Map.Entry<Variable, Term> entry : node.substitution().entrySet()) {
            entry.getKey().accept(this);
            entry.getValue().accept(this);
        }
        for (SymbolicConstraint.Equality equality : node.equalities()) {
            equality.leftHandSide().accept(this);
            equality.rightHandSide().accept(this);
        }
    }

    @Override public void visit(Term term) { }

    @Override
    public void visit(Token token) {
        visit((Term) token);
    }

    @Override
    public void visit(UninterpretedConstraint uninterpretedConstraint) {
        for (UninterpretedConstraint.Equality equality : uninterpretedConstraint.equalities()) {
            equality.leftHandSide().accept(this);
            equality.rightHandSide().accept(this);
        }
    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        visit((Term) uninterpretedToken);
    }

    @Override
    public void visit(Variable variable) {
        visit((Term) variable);
    }
    
    @Override
    public void visit(BuiltinMgu mgu) {
        visit((Term) mgu);
    }
}

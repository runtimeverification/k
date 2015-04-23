// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;

import java.util.Map;


/**
 * A bottom-up implementation of the visitor pattern.
 *
 * @author Traian
 */
public class PrePostVisitor implements Visitor {

    public CombinedLocalVisitor getPreVisitor() {
        return preVisitor;
    }

    public void setPreVisitor(CombinedLocalVisitor preVisitor) {
        this.preVisitor = preVisitor;
    }

    public CombinedLocalVisitor getPostVisitor() {
        return postVisitor;
    }

    public void setPostVisitor(CombinedLocalVisitor postVisitor) {
        this.postVisitor = postVisitor;
    }

    CombinedLocalVisitor preVisitor = new CombinedLocalVisitor();
    CombinedLocalVisitor postVisitor = new CombinedLocalVisitor();

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public void visit(BuiltinList node) {
        preVisitor.resetProceed();
        node.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        for (Term t : node.elementsLeft()) t.accept(this);
        for (Term t : node.baseTerms()) t.accept(this);
        for (Term t : node.elementsRight()) t.accept(this);
        node.accept(postVisitor);
    }

    @Override
    public void visit(BuiltinMap builtinMap) {
        preVisitor.resetProceed();
        builtinMap.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
            entry.getKey().accept(this);
            entry.getValue().accept(this);
        }
        for (Term term : builtinMap.baseTerms()) {
            term.accept(this);
        }
        builtinMap.accept(postVisitor);
    }

    @Override
    public void visit(BuiltinSet builtinSet) {
        preVisitor.resetProceed();
        builtinSet.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        for (Term term : builtinSet.elements()) {
            term.accept(this);
        }
        for (Term term : builtinSet.baseTerms()) {
            term.accept(this);
        }
        builtinSet.accept(postVisitor);
    }

    @Override public void visit(Term term) {
        preVisitor.resetProceed();
        term.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        term.accept(postVisitor);
    }

    @Override
    public void visit(CellCollection cellCollection) {
        preVisitor.resetProceed();
        cellCollection.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        for (CellCollection.Cell cell : cellCollection.cells().values()) {
            cell.content().accept(this);
        }
        for (Term term : cellCollection.baseTerms()) {
            term.accept(this);
        }
        cellCollection.accept(postVisitor);
    }

    @Override
    public void visit(Collection collection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void visit(Hole hole) {
        preVisitor.resetProceed();
        hole.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        hole.accept(postVisitor);
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        preVisitor.resetProceed();
        kLabelConstant.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        kLabelConstant.accept(postVisitor);
    }

    @Override
    public void visit(KLabelFreezer kLabelFreezer) {
        preVisitor.resetProceed();
        kLabelFreezer.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        kLabelFreezer.term().accept(this);
        kLabelFreezer.accept(postVisitor);
    }

    @Override
    public void visit(KLabelInjection kLabelInjection) {
        preVisitor.resetProceed();
        kLabelInjection.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        kLabelInjection.term().accept(this);
        kLabelInjection.accept(postVisitor);
    }

    @Override
    public void visit(InjectedKLabel injectedKLabel) {
        preVisitor.resetProceed();
        injectedKLabel.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        injectedKLabel.injectedKLabel().accept(this);
        injectedKLabel.accept(postVisitor);
    }

    @Override
    public void visit(KItem kItem) {
        preVisitor.resetProceed();
        kItem.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        kItem.kLabel().accept(this);
        kItem.kList().accept(this);
        kItem.accept(postVisitor);
    }

    @Override
    public void visit(KItemProjection kItemProjection) {
        preVisitor.resetProceed();
        kItemProjection.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        kItemProjection.term().accept(this);
        kItemProjection.accept(postVisitor);
    }

    @Override
    public void visit(Token token) {
        preVisitor.resetProceed();
        token.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        token.accept(postVisitor);
    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        preVisitor.resetProceed();
        uninterpretedToken.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        uninterpretedToken.accept(postVisitor);
    }

    @Override
    public void visit(BoolToken boolToken) {
        preVisitor.resetProceed();
        boolToken.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        boolToken.accept(postVisitor);
    }

    @Override
    public void visit(IntToken intToken) {
        preVisitor.resetProceed();
        intToken.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        intToken.accept(postVisitor);
    }

    @Override
    public void visit(BitVector bitVector) {
        preVisitor.resetProceed();
        bitVector.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        bitVector.accept(postVisitor);
    }

    @Override
    public void visit(KCollection kCollection) {
        preVisitor.resetProceed();
        kCollection.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        for (Term term : kCollection) {
            term.accept(this);
        }
        if (kCollection.hasFrame())
            kCollection.frame().accept(this);
        kCollection.accept(postVisitor);
    }

    @Override
    public void visit(KLabel kLabel) {
        preVisitor.resetProceed();
        kLabel.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        kLabel.accept(postVisitor);
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
        preVisitor.resetProceed();
        rule.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
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
        rule.accept(postVisitor);
    }

    @Override
    public void visit(ConjunctiveFormula node) {
        preVisitor.resetProceed();
        node.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
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
        node.accept(postVisitor);
    }

    @Override
    public void visit(DisjunctiveFormula node) {
        preVisitor.resetProceed();
        node.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        for (ConjunctiveFormula conjunctiveFormula : node.conjunctions()) {
            conjunctiveFormula.accept(this);
        }
        node.accept(postVisitor);
    }

    @Override
    public void visit(Variable variable) {
        visit((Term) variable);
    }

    @Override
    public void visit(ConstrainedTerm node) {
        // TODO(Traian): check if this fix is correct
        preVisitor.resetProceed();
        node.accept(preVisitor);
        if (!preVisitor.isProceed()) return;
        node.term().accept(this);
        node.constraint().accept(this);
        node.accept(postVisitor);
    }
}

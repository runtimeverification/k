package org.kframework.backend.java.symbolic;


import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KCollectionFragment;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 11:57 AM
 * To change this template use File | Settings | File Templates.
 */
public class BottomUpVisitor implements Visitor {

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override public void visit(Term term) { }

    @Override
    public void visit(BuiltinConstant builtinConstant) {
        visit((Term) builtinConstant);
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
        visit((Collection) cellCollection);
    }

    @Override
    public void visit(Collection collection) {
        if (collection.hasFrame()) {
            collection.getFrame().accept(this);
        }
        visit((Term) collection);
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        visit((KLabel) kLabelConstant);
    }

    @Override
    public void visit(Hole hole) {
        visit((Term) hole);
    }

    @Override
    public void visit(KLabelInjection kLabelInjection) {
        kLabelInjection.getTerm().accept(this);
        visit((KLabel) kLabelInjection);
    }

    @Override
    public void visit(KItem kItem) {
        kItem.getKLabel().accept(this);
        kItem.getKList().accept(this);
        visit((Term) kItem);
    }

    @Override
    public void visit(KCollection kCollection) {
        for (Term term : kCollection) {
            term.accept(this);
        }
        visit((Collection) kCollection);
    }

    @Override
    public void visit(KCollectionFragment kCollectionFragment) {
        for (Term term : kCollectionFragment) {
            term.accept(this);
        }
        visit((Collection) kCollectionFragment);
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
    public void visit(Map map) {
        for (java.util.Map.Entry<Term, Term> entry : map.getEntries().entrySet()) {
            entry.getKey().accept(this);
            entry.getValue().accept(this);
        }
        visit((Collection) map);
    }

    @Override
    public void visit(Rule rule) {
        rule.getLeftHandSide().accept(this);
        rule.getRightHandSide().accept(this);
        if (rule.hasCondition()) {
            rule.getCondition().accept(this);
        }
    }

    @Override
    public void visit(Variable variable) {
        visit((Term) variable);
    }

}

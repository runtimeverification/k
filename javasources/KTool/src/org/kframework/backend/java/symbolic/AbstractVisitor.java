package org.kframework.backend.java.symbolic;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 11:57 AM
 * To change this template use File | Settings | File Templates.
 */
public class AbstractVisitor implements Visitor {

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
    public void visit(ConstantKLabel constantKLabel) {
        visit((KLabel) constantKLabel);
    }

	@Override
	public void visit(Hole hole) { }

	@Override
    public void visit(InjectionKLabel injectionKLabel) {
        injectionKLabel.getTerm().accept(this);
        visit((KLabel) injectionKLabel);
    }

    @Override
    public void visit(K k) {
        k.getKLabel().accept(this);
        k.getKList().accept(this);
        visit((Term) k);
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
    public void visit(Variable variable) {
        visit((Term) variable);
    }

}

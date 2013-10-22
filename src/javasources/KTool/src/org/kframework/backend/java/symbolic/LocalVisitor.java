package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;

/**
 * @author Traian
 */
public class LocalVisitor implements Visitor {

    public boolean isProceed() {
        return proceed;
    }

    public void resetProceed() {
        this.proceed = true;
    }

    boolean proceed = true;

    @Override
    public String getName() {
        return null;  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void visit(BoolToken boolToken) {
        visit((Token) boolToken);
    }

    @Override
    public void visit(BuiltinList node) {
        visit((Collection) node);
    }

    @Override
    public void visit(BuiltinMap builtinMap) {
        visit((Collection) builtinMap);
    }

    @Override
    public void visit(BuiltinSet builtinSet) {
        visit((Collection) builtinSet);
    }

    @Override
    public void visit(Cell cell) {
        visit((Term) cell);
    }

    @Override
    public void visit(CellCollection cellCollection) {
        visit((Collection) cellCollection);
    }

    @Override
    public void visit(Collection collection) {
        visit((Term) collection);
    }

    @Override
    public void visit(ConstrainedTerm node) {
        visit((Term) node);
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
    public void visit(Int32Token intToken) {
        visit((Token) intToken);
    }

    protected void visit(JavaSymbolicObject object) {
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        visit((KLabel) kLabelConstant);
    }

    @Override
    public void visit(KLabelFreezer kLabelFreezer) {
        visit((KLabelInjection) kLabelFreezer);
    }

    @Override
    public void visit(KLabelInjection kLabelInjection) {
        visit((KLabel) kLabelInjection);
    }

    @Override
    public void visit(KItem kItem) {
        visit((Term) kItem);
    }

    @Override
    public void visit(KCollection kCollection) {
        visit((Collection) kCollection);
    }

    @Override
    public void visit(KCollectionFragment kCollectionFragment) {
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
    public void visit(ListLookup node) {
        visit((Term) node);
    }

    @Override
    public void visit(MapLookup mapLookup) {
        visit((Term) mapLookup);
    }

    @Override
    public void visit(MapUpdate mapUpdate) {
        visit((Term) mapUpdate);
    }

    @Override
    public void visit(MetaVariable metaVariable) {
        visit((Token) metaVariable);
    }

    @Override
    public void visit(Rule rule) {
        visit((JavaSymbolicObject) rule);
    }

    @Override
    public void visit(SetLookup mapLookup) {
        visit((Term) mapLookup);
    }

    @Override
    public void visit(SetUpdate mapUpdate) {
        visit((Term) mapUpdate);
    }

    @Override
    public void visit(SymbolicConstraint node) {
        visit((JavaSymbolicObject) node);
    }

    @Override
    public void visit(Term node) {
        visit((JavaSymbolicObject) node);
    }

    @Override
    public void visit(Token token) {
        visit((Term) token);
    }

    @Override
    public void visit(UninterpretedConstraint uninterpretedConstraint) {
        visit((JavaSymbolicObject) uninterpretedConstraint);
    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        visit((Token) uninterpretedToken);
    }

    @Override
    public void visit(Variable variable) {
        visit((Term) variable);
    }
}

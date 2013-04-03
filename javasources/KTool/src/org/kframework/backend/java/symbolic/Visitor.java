package org.kframework.backend.java.symbolic;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 11:50 AM
 * To change this template use File | Settings | File Templates.
 */
public interface Visitor {

    public String getName();

    public void visit(BuiltinConstant builtinConstant);
    public void visit(Cell cell);
    public void visit(CellCollection cellCollection);
    public void visit(Collection collection);
    public void visit(ConstantKLabel constantKLabel);
    public void visit(Hole hole);
    public void visit(InjectionKLabel injectionKLabel);
    public void visit(K k);
    public void visit(KCollection kCollection);
    public void visit(KCollectionFragment kCollectionFragment);
    public void visit(KLabel kLabel);
    public void visit(KList kList);
    public void visit(KSequence kSequence);
    public void visit(Map map);
    public void visit(Term node);
    public void visit(Variable variable);

}

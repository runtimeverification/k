package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 4:22 PM
 * To change this template use File | Settings | File Templates.
 */
public interface Transformer {

    public String getName();

    public ASTNode transform(BuiltinConstant builtinConstant);
    public ASTNode transform(Cell cell);
    public ASTNode transform(CellCollection cellCollection);
    public ASTNode transform(Collection collection);
    public ASTNode transform(ConstantKLabel constantKLabel);
    public ASTNode transform(Hole hole);
    public ASTNode transform(InjectionKLabel injectionKLabel);
    public ASTNode transform(K k);
    public ASTNode transform(KCollection kCollection);
    public ASTNode transform(KLabel kLabel);
    public ASTNode transform(KList kList);
    public ASTNode transform(KSequence kSequence);
    public ASTNode transform(Map map);
    public ASTNode transform(Term node);
    public ASTNode transform(Variable variable);
}

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.ConstantKLabel;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.InjectionKLabel;
import org.kframework.backend.java.kil.K;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
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

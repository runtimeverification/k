package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.BoolToken;
import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.IntToken;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.UninterpretedToken;
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
    public ASTNode transform(KLabelConstant kLabelConstant);
    public ASTNode transform(Hole hole);
    public ASTNode transform(KLabelInjection kLabelInjection);
    public ASTNode transform(KItem kItem);
    public ASTNode transform(Token token);
    public ASTNode transform(UninterpretedToken uninterpretedToken);
    public ASTNode transform(BoolToken boolToken);
    public ASTNode transform(IntToken intToken);
    public ASTNode transform(KCollection kCollection);
    public ASTNode transform(KLabel kLabel);
    public ASTNode transform(KList kList);
    public ASTNode transform(KSequence kSequence);
    public ASTNode transform(Map map);
    public ASTNode transform(MapLookup mapLookup);
    public ASTNode transform(MapUpdate mapUpdate);
    public ASTNode transform(Rule rule);
    public ASTNode transform(Term node);
    public ASTNode transform(Variable variable);

}

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.kil.ASTNode;


/**
 * Interface for a visitor pattern which constructs a new AST node.
 *
 * @author AndreiS
 */
public interface Transformer {

    public String getName();

    public ASTNode transform(BoolToken boolToken);
    public ASTNode transform(BuiltinMap builtinMap);
    public ASTNode transform(BuiltinSet builtinSet);
    public ASTNode transform(Cell cell);
    public ASTNode transform(CellCollection cellCollection);
    public ASTNode transform(Collection collection);
    public ASTNode transform(Hole hole);
    public ASTNode transform(IntToken intToken);
    public ASTNode transform(KLabelConstant kLabelConstant);
    public ASTNode transform(KLabelFreezer kLabelFreezer);
    public ASTNode transform(KLabelInjection kLabelInjection);
    public ASTNode transform(KItem kItem);
    public ASTNode transform(KCollection kCollection);
    public ASTNode transform(KLabel kLabel);
    public ASTNode transform(KList kList);
    public ASTNode transform(KSequence kSequence);
    public ASTNode transform(MapLookup mapLookup);
    public ASTNode transform(MapUpdate mapUpdate);
    public ASTNode transform(MetaVariable metaVariable);
    public ASTNode transform(Term node);
    public ASTNode transform(Token token);
    public ASTNode transform(UninterpretedToken uninterpretedToken);
    public ASTNode transform(Variable variable);

}

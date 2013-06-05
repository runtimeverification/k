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
import org.kframework.backend.java.kil.KCollectionFragment;
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
    public void visit(KLabelConstant kLabelConstant);
    public void visit(Hole hole);
    public void visit(KLabelInjection kLabelInjection);
    public void visit(KItem kItem);
    public void visit(Token token);
    public void visit(UninterpretedToken uninterpretedToken);
    public void visit(BoolToken boolToken);
    public void visit(IntToken intToken);
    public void visit(KCollection kCollection);
    public void visit(KCollectionFragment kCollectionFragment);
    public void visit(KLabel kLabel);
    public void visit(KList kList);
    public void visit(KSequence kSequence);
    public void visit(Map map);
    public void visit(MapLookup mapLookup);
    public void visit(MapUpdate mapUpdate);
    public void visit(Rule rule);
    public void visit(Term node);
    public void visit(Variable variable);

}

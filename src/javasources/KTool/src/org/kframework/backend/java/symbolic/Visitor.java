package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KCollectionFragment;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.ListLookup;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.SetLookup;
import org.kframework.backend.java.kil.SetUpdate;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermCons;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;


/**
 * Interface for a visitor pattern.
 *
 * @author AndreiS
 */
public interface Visitor {

    public String getName();

    public void visit(BoolToken boolToken);
    public void visit(BuiltinList builtinList);
    public void visit(BuiltinMap builtinMap);
    public void visit(BuiltinSet builtinSet);
    public void visit(Cell cell);
    public void visit(CellCollection cellCollection);
    public void visit(Collection collection);
    public void visit(ConstrainedTerm constrainedTerm);
    public void visit(Hole hole);
    public void visit(IntToken intToken);
    public void visit(Int32Token intToken);
    public void visit(KLabelConstant kLabelConstant);
    public void visit(KLabelFreezer kLabelFreezer);
    public void visit(KLabelInjection kLabelInjection);
    public void visit(KItem kItem);
    public void visit(KCollection kCollection);
    public void visit(KCollectionFragment kCollectionFragment);
    public void visit(KLabel kLabel);
    public void visit(KList kList);
    public void visit(KSequence kSequence);
    public void visit(ListLookup listLookup);
    public void visit(MapLookup mapLookup);
    public void visit(MapUpdate mapUpdate);
    public void visit(MetaVariable metaVariable);
    public void visit(Rule rule);
    public void visit(SetLookup mapLookup);
    public void visit(SetUpdate mapUpdate);
    public void visit(SymbolicConstraint node);
    public void visit(Term node);
    public void visit(TermCons termCons);
    public void visit(Token token);
    public void visit(UninterpretedConstraint uninterpretedConstraint);
    public void visit(UninterpretedToken uninterpretedToken);
    public void visit(Variable variable);

}

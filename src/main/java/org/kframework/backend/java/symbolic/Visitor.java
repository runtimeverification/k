// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;


/**
 * Interface for a visitor pattern.
 *
 * @author AndreiS
 */
public interface Visitor {

    public String getName();

    public void visit(BitVector bitVector);
    public void visit(BoolToken boolToken);
    public void visit(BuiltinList builtinList);
    public void visit(BuiltinMap builtinMap);
    public void visit(BuiltinSet builtinSet);
    public void visit(BuiltinMgu builtinMgu);
    public void visit(Cell cell);
    public void visit(CellCollection cellCollection);
    public void visit(Collection collection);
    public void visit(ConstrainedTerm constrainedTerm);
    public void visit(Hole hole);
    public void visit(IntToken intToken);
    public void visit(KLabelConstant kLabelConstant);
    public void visit(KLabelFreezer kLabelFreezer);
    public void visit(KLabelInjection kLabelInjection);
    public void visit(KItem kItem);
    public void visit(KItemProjection kItemProjection);
    public void visit(KCollection kCollection);
    public void visit(KLabel kLabel);
    public void visit(KList kList);
    public void visit(KSequence kSequence);
    public void visit(ListLookup listLookup);
    public void visit(ListUpdate listUpdate);
    public void visit(MapKeyChoice mapKeyChoice);
    public void visit(MapLookup mapLookup);
    public void visit(MapUpdate mapUpdate);
    public void visit(MetaVariable metaVariable);
    public void visit(Rule rule);
    public void visit(SetElementChoice setElementChoice);
    public void visit(SetLookup mapLookup);
    public void visit(SetUpdate mapUpdate);
    public void visit(SymbolicConstraint node);
    public void visit(Term node);
    public void visit(Token token);
    public void visit(UninterpretedConstraint uninterpretedConstraint);
    public void visit(UninterpretedToken uninterpretedToken);
    public void visit(Variable variable);

}

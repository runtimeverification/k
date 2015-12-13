// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;


/**
 * Interface for a visitor pattern.
 *
 * @author AndreiS
 */
public interface Visitor {

    String getName();

    void visit(BitVector bitVector);
    void visit(BoolToken boolToken);
    void visit(BuiltinList builtinList);
    void visit(BuiltinMap builtinMap);
    void visit(BuiltinSet builtinSet);
    void visit(CellCollection cellCollection);
    void visit(Collection collection);
    void visit(ConjunctiveFormula node);
    void visit(ConstrainedTerm constrainedTerm);
    void visit(DisjunctiveFormula node);
    void visit(Hole hole);
    void visit(IntToken intToken);
    void visit(KLabelConstant kLabelConstant);
    void visit(KLabelFreezer kLabelFreezer);
    void visit(KLabelInjection kLabelInjection);
    void visit(KItem kItem);
    void visit(KItemProjection kItemProjection);
    void visit(KCollection kCollection);
    void visit(KLabel kLabel);
    void visit(KList kList);
    void visit(KSequence kSequence);
    void visit(MetaVariable metaVariable);
    void visit(Rule rule);
    void visit(Term node);
    void visit(Token token);
    void visit(UninterpretedToken uninterpretedToken);
    void visit(Variable variable);
    void visit(InjectedKLabel injectedKLabel);
    void visit(RuleAutomatonDisjunction ruleAutomatonDisjunction);
    void visit(InnerRHSRewrite innerRHSRewrite);
}

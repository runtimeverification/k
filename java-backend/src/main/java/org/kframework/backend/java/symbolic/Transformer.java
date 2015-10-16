// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;


/**
 * Interface for a visitor pattern which constructs a new AST node.
 *
 * @author AndreiS
 */
public interface Transformer {

    String getName();

    ASTNode transform(BitVector bitVector);
    ASTNode transform(BoolToken boolToken);
    ASTNode transform(BuiltinList builtinList);
    ASTNode transform(BuiltinMap builtinMap);
    ASTNode transform(BuiltinSet builtinSet);
    ASTNode transform(CellCollection cellCollection);
    ASTNode transform(Collection collection);
    ASTNode transform(ConjunctiveFormula conjunctiveFormula);
    ASTNode transform(ConstrainedTerm constrainedTerm);
    ASTNode transform(DisjunctiveFormula disjunctiveFormula);
    ASTNode transform(FloatToken floatToken);
    ASTNode transform(Hole hole);
    ASTNode transform(IntToken intToken);
    ASTNode transform(KLabelConstant kLabelConstant);
    ASTNode transform(KLabelFreezer kLabelFreezer);
    ASTNode transform(KLabelInjection kLabelInjection);
    ASTNode transform(KItemProjection kItemProjection);
    ASTNode transform(KItem kItem);
    ASTNode transform(KCollection kCollection);
    ASTNode transform(KLabel kLabel);
    ASTNode transform(KList kList);
    ASTNode transform(KSequence kSequence);
    ASTNode transform(MetaVariable metaVariable);
    ASTNode transform(Rule rule);
    ASTNode transform(StringToken stringToken);
    ASTNode transform(Term node);
    ASTNode transform(Token token);
    ASTNode transform(UninterpretedToken uninterpretedToken);
    ASTNode transform(Variable variable);
    ASTNode transform(InjectedKLabel injectedKLabel);
    ASTNode transform(RuleAutomatonDisjunction ruleAutomatonDisjunction);
    ASTNode transform(InnerRHSRewrite innerRHSRewrite);
}

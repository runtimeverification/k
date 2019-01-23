// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;


/**
 * Interface for a visitor pattern which constructs a new AST node.
 *
 * @author AndreiS
 */
public interface Transformer {

    String getName();

    JavaSymbolicObject transform(BitVector bitVector);
    JavaSymbolicObject transform(BoolToken boolToken);
    JavaSymbolicObject transform(BuiltinList builtinList);
    JavaSymbolicObject transform(BuiltinMap builtinMap);
    JavaSymbolicObject transform(BuiltinSet builtinSet);

    JavaSymbolicObject transform(Collection collection);
    JavaSymbolicObject transform(ConjunctiveFormula conjunctiveFormula);
    JavaSymbolicObject transform(ConstrainedTerm constrainedTerm);
    JavaSymbolicObject transform(DisjunctiveFormula disjunctiveFormula);
    JavaSymbolicObject transform(FloatToken floatToken);
    JavaSymbolicObject transform(Hole hole);
    JavaSymbolicObject transform(IntToken intToken);
    JavaSymbolicObject transform(KLabelConstant kLabelConstant);

    JavaSymbolicObject transform(KLabelInjection kLabelInjection);
    JavaSymbolicObject transform(KItemProjection kItemProjection);
    JavaSymbolicObject transform(KItem kItem);
    JavaSymbolicObject transform(KCollection kCollection);
    JavaSymbolicObject transform(KLabel kLabel);
    JavaSymbolicObject transform(KList kList);
    JavaSymbolicObject transform(KSequence kSequence);
    JavaSymbolicObject transform(MetaVariable metaVariable);
    JavaSymbolicObject transform(Rule rule);
    JavaSymbolicObject transform(StringToken stringToken);
    JavaSymbolicObject transform(Term node);
    JavaSymbolicObject transform(Token token);
    JavaSymbolicObject transform(UninterpretedToken uninterpretedToken);
    JavaSymbolicObject transform(Variable variable);
    JavaSymbolicObject transform(InjectedKLabel injectedKLabel);
    JavaSymbolicObject transform(RuleAutomatonDisjunction ruleAutomatonDisjunction);
    JavaSymbolicObject transform(InnerRHSRewrite innerRHSRewrite);
    default JavaSymbolicObject transform(SMTLibTerm smtLibTerm) {
        return smtLibTerm;
    }
}

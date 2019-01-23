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
 * Performs transformation on a given node without doing tree traversal. This
 * class serves as an adapter class: method {@code transform} simply recurs with
 * its argument being casted to a super-class until that argument becomes a
 * {@code JavaSymbolicObject}.
 *
 * @author Traian
 */
public class LocalTransformer implements Transformer {

    @Override
    public String getName() {
        return "Identity Transformer";
    }

    @Override
    public JavaSymbolicObject transform(BitVector bitVector) {
        return transform((Token) bitVector);
    }

    @Override
    public JavaSymbolicObject transform(BoolToken boolToken) {
        return transform((Token) boolToken);
    }

    @Override
    public JavaSymbolicObject transform(BuiltinList builtinList) {
        return transform((Collection) builtinList);
    }

    @Override
    public JavaSymbolicObject transform(BuiltinMap builtinMap) {
        return transform((Collection) builtinMap);
    }

    @Override
    public JavaSymbolicObject transform(BuiltinSet builtinSet) {
        return transform((Collection) builtinSet);
    }

    @Override
    public JavaSymbolicObject transform(Collection collection) {
        return transform((Term) collection);
    }

    @Override
    public JavaSymbolicObject transform(ConstrainedTerm constrainedTerm) {
        return transform((JavaSymbolicObject) constrainedTerm);
    }

    @Override
    public JavaSymbolicObject transform(FloatToken floatToken) {
        return transform((Token) floatToken);
    }

    @Override
    public JavaSymbolicObject transform(Hole hole) {
        return transform((Term) hole);
    }

    @Override
    public JavaSymbolicObject transform(IntToken intToken) {
        return transform((Token) intToken);
    }

    @Override
    public JavaSymbolicObject transform(KLabelConstant kLabelConstant) {
        return transform((KLabel) kLabelConstant);
    }

    @Override
    public JavaSymbolicObject transform(KLabelInjection kLabelInjection) {
        return transform((KLabel) kLabelInjection);
    }

    @Override
    public JavaSymbolicObject transform(KItemProjection kItemProjection) {
        return transform((Term) kItemProjection);
    }

    @Override
    public JavaSymbolicObject transform(KItem kItem) {
        return transform((Term) kItem);
    }

    @Override
    public JavaSymbolicObject transform(KCollection kCollection) {
        return transform((Collection) kCollection);
    }

    @Override
    public JavaSymbolicObject transform(KLabel kLabel) {
        return transform((Term) kLabel);
    }

    @Override
    public JavaSymbolicObject transform(KList kList) {
        return transform((KCollection) kList);
    }

    @Override
    public JavaSymbolicObject transform(KSequence kSequence) {
        return transform((KCollection) kSequence);
    }

    @Override
    public JavaSymbolicObject transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public JavaSymbolicObject transform(Rule rule) {
        return transform((JavaSymbolicObject) rule);
    }

    protected JavaSymbolicObject transform(JavaSymbolicObject object) {
        return object;
    }

    @Override
    public JavaSymbolicObject transform(ConjunctiveFormula conjunctiveFormula) {
        return transform((Term) conjunctiveFormula);
    }

    @Override
    public JavaSymbolicObject transform(DisjunctiveFormula disjunctiveFormula) {
        return transform((Term) disjunctiveFormula);
    }

    @Override
    public JavaSymbolicObject transform(StringToken stringToken) {
        return transform((Token) stringToken);
    }

    @Override
    public JavaSymbolicObject transform(Term node) {
        return transform((JavaSymbolicObject) node);
    }

    @Override
    public JavaSymbolicObject transform(Token token) {
        return transform((Term) token);
    }

    @Override
    public JavaSymbolicObject transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
    }

    @Override
    public JavaSymbolicObject transform(Variable variable) {
        return transform((Term) variable);
    }

    @Override
    public JavaSymbolicObject transform(InjectedKLabel injectedKLabel) {
        return transform((Term) injectedKLabel);
    }

    @Override
    public JavaSymbolicObject transform(RuleAutomatonDisjunction ruleAutomatonDisjunction) {
        return transform((JavaSymbolicObject) ruleAutomatonDisjunction);
    }

    @Override
    public JavaSymbolicObject transform(InnerRHSRewrite innerRHSRewrite) {
        return transform((JavaSymbolicObject) innerRHSRewrite);
    }
}

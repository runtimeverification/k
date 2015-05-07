// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

/**
 * Performs transformation on a given node without doing tree traversal. This
 * class serves as an adapter class: method {@code transform} simply recurs with
 * its argument being casted to a super-class until that argument becomes a
 * {@code JavaSymbolicObject}.
 *
 * @author Traian
 */
public class LocalTransformer implements Transformer {

    protected final TermContext context;

    public LocalTransformer() {
        this.context = null;
    }

    public LocalTransformer(TermContext context) {
        this.context = context;
    }

    @Override
    public String getName() {
        return "Identity Transformer";
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        return transform((Token) bitVector);
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return transform((Token) boolToken);
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        return transform((Collection) builtinList);
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        return transform((Collection) builtinMap);
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        return transform((Collection) builtinSet);
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        return transform((Collection) cellCollection);
    }

    @Override
    public ASTNode transform(Collection collection) {
        return transform((Term) collection);
    }

    @Override
    public ASTNode transform(ConstrainedTerm constrainedTerm) {
        return transform((JavaSymbolicObject) constrainedTerm);
    }

    @Override
    public ASTNode transform(FloatToken floatToken) {
        return transform((Token) floatToken);
    }

    @Override
    public ASTNode transform(Hole hole) {
        return transform((Term) hole);
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return transform((Token) intToken);
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        return transform((KLabel) kLabelConstant);
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        return transform((KLabelInjection) kLabelFreezer);
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        return transform((KLabel) kLabelInjection);
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        return transform((Term) kItemProjection);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return transform((Term) kItem);
    }

    @Override
    public ASTNode transform(KCollection kCollection) {
        return transform((Collection) kCollection);
    }

    @Override
    public ASTNode transform(KLabel kLabel) {
        return transform((Term) kLabel);
    }

    @Override
    public ASTNode transform(KList kList) {
        return transform((KCollection) kList);
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        return transform((KCollection) kSequence);
    }

    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public ASTNode transform(Rule rule) {
        return transform((JavaSymbolicObject) rule);
    }

    protected ASTNode transform(JavaSymbolicObject object) {
        return object;
    }

    @Override
    public ASTNode transform(ConjunctiveFormula conjunctiveFormula) {
        return transform((Term) conjunctiveFormula);
    }

    @Override
    public ASTNode transform(DisjunctiveFormula disjunctiveFormula) {
        return transform((Term) disjunctiveFormula);
    }

    @Override
    public ASTNode transform(StringToken stringToken) {
        return transform((Token) stringToken);
    }

    @Override
    public ASTNode transform(Term node) {
        return transform((JavaSymbolicObject) node);
    }

    @Override
    public ASTNode transform(Token token) {
        return transform((Term) token);
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
    }

    @Override
    public ASTNode transform(Variable variable) {
        return transform((Term) variable);
    }

    @Override
    public ASTNode transform(InjectedKLabel injectedKLabel) {
        return transform((Term) injectedKLabel);
    }
}

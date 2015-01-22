// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.Map;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

/**
 * Transformer that substitutes (in a binder-sensitive way) and evaluates a
 * {@code Term} according to given substitution map.
 * <p>
 * Comparing to the implementation using {@link PrePostTransformer} and
 * {@link LocalTransformer}, this implementation derives
 * {@link CopyOnWriteTransformer} directly and, thus, is much more efficient.
 *
 * @author YilongL
 *
 */
public class SubstituteAndEvaluateTransformer extends CopyOnWriteTransformer {

    protected final Map<Variable, ? extends Term> substitution;

    protected boolean copyOnShareSubstAndEval = false;

    /*
     * YilongL: it turns out that not doing variableSet update along with
     * substituteAndEvaluate costs significant overhead; not sure why but I am
     * leaving variableSet as lazily computed
     */

    public SubstituteAndEvaluateTransformer(Map<Variable, ? extends Term> substitution, TermContext context) {
        super(context);
        this.substitution = substitution;
    }

    protected boolean proceed(JavaSymbolicObject object) {
        return object.canSubstituteAndEvaluate(substitution);
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        return bitVector;
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return boolToken;
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        /* YilongL: cannot extract the following code to a common helper method
         * without involving dynamic dispatch */
        return proceed(builtinList) ? super.transform(builtinList) : builtinList;
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        return proceed(builtinMap) ? super.transform(builtinMap) : builtinMap;
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        return proceed(builtinSet) ? super.transform(builtinSet) : builtinSet;
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        return proceed(cellCollection) ? super.transform(cellCollection) : cellCollection;
    }

    @Override
    public ASTNode transform(Hole hole) {
        return hole;
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return intToken;
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        return kLabelConstant;
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        return proceed(kLabelFreezer) ? super.transform(kLabelFreezer) : kLabelFreezer;
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        return proceed(kLabelInjection) ? super.transform(kLabelInjection) : kLabelInjection;
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        return proceed(kItemProjection) ?
                ((KItemProjection) super.transform(kItemProjection)).evaluateProjection() :
                kItemProjection;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        Term result = kItem;
        if (proceed(kItem)) {
            result = ((KItem) super
                    .transform(BinderSubstitutionTransformer.binderSensitiveSubstitute(kItem, context)))
                    .resolveFunctionAndAnywhere(copyOnShareSubstAndEval, context);
        }

        return result;
    }

    @Override
    public ASTNode transform(KList kList) {
        return proceed(kList) ? super.transform(kList) : kList;
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        return proceed(kSequence) ? super.transform(kSequence) : kSequence;
    }

    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return metaVariable;
    }

    @Override
    public ASTNode transform(Rule rule) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(SymbolicConstraint symbolicConstraint) {
        return proceed(symbolicConstraint) ? super.transform(symbolicConstraint) : symbolicConstraint;
    }

    @Override
    public ASTNode transform(StringToken stringToken) {
        return stringToken;
    }

    @Override
    public ASTNode transform(UninterpretedConstraint uninterpretedConstraint) {
        return proceed(uninterpretedConstraint) ? super.transform(uninterpretedConstraint) : uninterpretedConstraint;
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return uninterpretedToken;
    }

    @Override
    public ASTNode transform(Variable variable) {
        Term term = substitution.get(variable);
        return term == null ? variable : term;
    }

}

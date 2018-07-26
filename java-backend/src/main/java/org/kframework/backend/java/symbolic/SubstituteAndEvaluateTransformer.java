// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;

import java.util.Map;

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
        return object.canSubstituteAndEvaluate(substitution, context);
    }

    @Override
    public JavaSymbolicObject transform(BitVector bitVector) {
        return bitVector;
    }

    @Override
    public JavaSymbolicObject transform(BoolToken boolToken) {
        return boolToken;
    }

    @Override
    public JavaSymbolicObject transform(BuiltinList builtinList) {
        /* YilongL: cannot extract the following code to a common helper method
         * without involving dynamic dispatch */
        return proceed(builtinList) ? super.transform(builtinList) : builtinList;
    }

    @Override
    public JavaSymbolicObject transform(BuiltinMap builtinMap) {
        return proceed(builtinMap) ? super.transform(builtinMap) : builtinMap;
    }

    @Override
    public JavaSymbolicObject transform(BuiltinSet builtinSet) {
        return proceed(builtinSet) ? super.transform(builtinSet) : builtinSet;
    }

    @Override
    public JavaSymbolicObject transform(Hole hole) {
        return hole;
    }

    @Override
    public JavaSymbolicObject transform(IntToken intToken) {
        return intToken;
    }

    @Override
    public JavaSymbolicObject transform(KLabelConstant kLabelConstant) {
        return kLabelConstant;
    }

    @Override
    public JavaSymbolicObject transform(KLabelInjection kLabelInjection) {
        return proceed(kLabelInjection) ? super.transform(kLabelInjection) : kLabelInjection;
    }

    @Override
    public JavaSymbolicObject transform(KItemProjection kItemProjection) {
        return proceed(kItemProjection) ?
                ((KItemProjection) super.transform(kItemProjection)).evaluateProjection() :
                kItemProjection;
    }

    @Override
    public JavaSymbolicObject transform(KItem kItem) {
        Term result = kItem;
        if (proceed(kItem)) {
            result = ((KItem) super
                    .transform(BinderSubstitutionTransformer.binderSensitiveSubstitute(kItem)))
                    .resolveFunctionAndAnywhere(context);
        }

        return result;
    }

    @Override
    public JavaSymbolicObject transform(KList kList) {
        return proceed(kList) ? super.transform(kList) : kList;
    }

    @Override
    public JavaSymbolicObject transform(KSequence kSequence) {
        return proceed(kSequence) ? super.transform(kSequence) : kSequence;
    }

    @Override
    public JavaSymbolicObject transform(MetaVariable metaVariable) {
        return metaVariable;
    }

    @Override
    public JavaSymbolicObject transform(Rule rule) {
        throw new UnsupportedOperationException();
    }

    @Override
    public JavaSymbolicObject transform(ConjunctiveFormula conjunctiveFormula) {
        return proceed(conjunctiveFormula) ? super.transform(conjunctiveFormula) : conjunctiveFormula;
    }

    @Override
    public JavaSymbolicObject transform(DisjunctiveFormula disjunctiveFormula) {
        return proceed(disjunctiveFormula) ? super.transform(disjunctiveFormula) : disjunctiveFormula;
    }

    @Override
    public JavaSymbolicObject transform(StringToken stringToken) {
        return stringToken;
    }

    @Override
    public JavaSymbolicObject transform(UninterpretedToken uninterpretedToken) {
        return uninterpretedToken;
    }

    @Override
    public JavaSymbolicObject transform(Variable variable) {
        Term term = substitution.get(variable);
        return term == null ? variable : term;
    }

}

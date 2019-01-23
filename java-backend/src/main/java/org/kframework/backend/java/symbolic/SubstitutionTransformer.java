// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.Sets;
import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;

import java.util.Map;


/**
 * Substitutes variables with terms according to a given substitution map.
 *
 * @author AndreiS
 */
public class SubstitutionTransformer extends CopyOnWriteTransformer {

    protected final Map<Variable, ? extends Term> substitution;

    public SubstitutionTransformer(Map<Variable, ? extends Term> substitution) {
        super();
        this.substitution = substitution;
    }

    protected boolean proceed(JavaSymbolicObject object) {
        return !Sets.intersection(object.variableSet(), substitution.keySet()).isEmpty();
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
    public JavaSymbolicObject transform(ConstrainedTerm constrainedTerm) {
        return proceed(constrainedTerm) ? super.transform(constrainedTerm) : constrainedTerm;
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
        return proceed(kItemProjection) ? super.transform(kItemProjection) : kItemProjection;
    }

    @Override
    public JavaSymbolicObject transform(KItem kItem) {
        return proceed(kItem) ? super.transform(kItem) : kItem;
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
        return proceed(rule) ? super.transform(rule) : rule;
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

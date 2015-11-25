// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import com.google.common.collect.Sets;

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
    public ASTNode transform(ConstrainedTerm constrainedTerm) {
        return proceed(constrainedTerm) ? super.transform(constrainedTerm) : constrainedTerm;
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
        return proceed(kItemProjection) ? super.transform(kItemProjection) : kItemProjection;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return proceed(kItem) ? super.transform(kItem) : kItem;
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
        return proceed(rule) ? super.transform(rule) : rule;
    }

    @Override
    public ASTNode transform(ConjunctiveFormula conjunctiveFormula) {
        return proceed(conjunctiveFormula) ? super.transform(conjunctiveFormula) : conjunctiveFormula;
    }

    @Override
    public ASTNode transform(DisjunctiveFormula disjunctiveFormula) {
        return proceed(disjunctiveFormula) ? super.transform(disjunctiveFormula) : disjunctiveFormula;
    }

    @Override
    public ASTNode transform(StringToken stringToken) {
        return stringToken;
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

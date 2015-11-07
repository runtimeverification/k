// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Expands map patterns according to their definitions.
 */
public class PatternExpander extends CopyOnWriteTransformer {

    private final ConjunctiveFormula constraint;
    private final boolean narrowing;

    private ConjunctiveFormula extraConstraint;

    public PatternExpander(ConjunctiveFormula constraint, boolean narrowing, TermContext context) {
        super(context);
        this.constraint = constraint;
        this.narrowing = narrowing;
        extraConstraint = ConjunctiveFormula.of(context.global());
    }

    public ConjunctiveFormula extraConstraint() {
        return extraConstraint;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        kItem = (KItem) super.transform(kItem);
        if (constraint == null) {
            return kItem;
        }

        if (!(kItem.kLabel() instanceof KLabelConstant
                && ((KLabelConstant) kItem.kLabel()).isPattern()
                && kItem.kList() instanceof KList)) {
            return kItem;
        }
        KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();

        List<ConstrainedTerm> results = new ArrayList<>();
        Term inputKList = KList.concatenate(kItem.getPatternInput());
        Term outputKList = KList.concatenate(kItem.getPatternOutput());
        for (Rule rule : kItem.globalContext().getDefinition().patternRules().get(kLabel)) {
            Term ruleInputKList = KList.concatenate(((KItem) rule.leftHandSide()).getPatternInput());
            Term ruleOutputKList = KList.concatenate(((KItem) rule.leftHandSide()).getPatternOutput());
            ConjunctiveFormula unificationConstraint = ConjunctiveFormula.of(context.global())
                    .add(inputKList, ruleInputKList)
                    .simplify(context);
            // TODO(AndreiS): there is only one solution here, so no list of constraints
            if (unificationConstraint.isFalse()) {
                continue;
            }

            if (narrowing) {
                ConjunctiveFormula globalConstraint = unificationConstraint
                        .addAll(constraint.equalities())
                        .addAll(rule.requires())
                        .simplify(context);
                if (globalConstraint.isFalse() || globalConstraint.checkUnsat()) {
                    continue;
                }
                globalConstraint = globalConstraint
                        .add(outputKList, ruleOutputKList)
                        .addAll(rule.ensures())
                        .simplify(context);
                if (globalConstraint.isFalse() || globalConstraint.checkUnsat()) {
                    continue;
                }
            } else {
                Set<Variable> existVariables = ruleInputKList.variableSet();
                unificationConstraint = unificationConstraint.orientSubstitution(existVariables);
                if (!unificationConstraint.isMatching(existVariables)) {
                    continue;
                }

                ConjunctiveFormula requires = unificationConstraint
                        .addAll(rule.requires())
                        .simplify(context);
                // this should be guaranteed by the above unificationConstraint.isMatching
                assert requires.substitution().keySet().containsAll(existVariables);
                if (requires.isFalse() || !constraint.implies(requires, existVariables)) {
                    continue;
                }
            }

            unificationConstraint = unificationConstraint
                    .add(outputKList, ruleOutputKList)
                    .addAll(rule.ensures())
                    .simplify(context);
            if (!unificationConstraint.isFalse() && !unificationConstraint.checkUnsat()) {
                results.add(SymbolicRewriter.buildResult(rule, unificationConstraint, null, false, context));
            }
        }

        if (results.size() == 1) {
            extraConstraint = extraConstraint.add(results.get(0).constraint()).simplify(context);
            return results.get(0).term().accept(this);
        } else {
            return kItem;
        }
    }

}

package org.kframework.backend.java.symbolic;

import com.google.common.collect.Sets;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.Attribute;

import java.util.List;

/**
 * Created by andrei on 6/4/14.
 */
public class PatternExpander extends PrePostTransformer {

    private PatternExpander(List<KItem> patterns, SymbolicConstraint constraint, TermContext context) {
        super(context);
        this.getPostTransformer().addTransformer(new LocalPatternExpander(patterns, context, constraint));
    }

    public static Term evaluate(List<KItem> patterns, Term term, SymbolicConstraint constraint, TermContext context) {
        return (Term) term.accept(new PatternExpander(patterns, constraint, context));
    }

    private static class LocalPatternExpander extends LocalTransformer {

        private final List<KItem> patterns;
        /**
        * The symbolic constraint of the {@code ConstrainedTerm} which contains the
        * terms to be evaluated by this evaluator.
        */
        private final SymbolicConstraint constraint;

        public LocalPatternExpander(List<KItem> patterns, TermContext context, SymbolicConstraint constraint) {
            super(context);
            this.patterns = patterns;
            this.constraint = constraint;
        }

        @Override
        public Term transform(KItem kItem) {
            if (!patterns.contains(kItem)) {
                return kItem;
            }

            KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();
            KList kList = (KList) kItem.kList();
            int inputCount = Integer.parseInt(kLabel.productions().get(0).getAttribute(Attribute.PATTERN_KEY));
            KList inputKList = new KList(kList.getContents().subList(0, inputCount));
            KList outputKList = new KList(kList.getContents().subList(inputCount, kList.getContents().size()));
            for (Rule rule : context.definition().patternRules().get(kLabel)) {
                KList ruleInputKList = new KList(((KList) ((KItem) rule.leftHandSide()).kList()).getContents().subList(0, inputCount));
                KList ruleOutputKList = new KList(((KList) ((KItem) rule.leftHandSide()).kList()).getContents().subList(inputCount, kList.getContents().size()));
                SymbolicConstraint unificationConstraint = new SymbolicConstraint(context);
                unificationConstraint.add(inputKList, ruleInputKList);
                unificationConstraint.simplify();
                // TODO(AndreiS): there is only one solution here, so no list of constraints
                if (unificationConstraint.isFalse() || unificationConstraint.isMatching(ruleInputKList.variableSet())) {
                    continue;
                }

                SymbolicConstraint ruleCondition = new SymbolicConstraint(context);
                ruleCondition.addAll(rule.requires());
                ruleCondition.substitute(unificationConstraint.substitution(), context);
                assert Sets.intersection(ruleCondition.variableSet(), ruleInputKList.variableSet()).isEmpty();

                if (!constraint.implies(ruleCondition)) {
                    continue;
                }

                unificationConstraint.add(outputKList, ruleOutputKList);
                unificationConstraint.simplify();
                if (unificationConstraint.isFalse()) {
                    continue;
                }

                // TODO(AndreiS): only one solution is required
                return SymbolicRewriter.constructNewSubjectTerm(rule, unificationConstraint).term();
            }

            return kItem;
        }
    }
}

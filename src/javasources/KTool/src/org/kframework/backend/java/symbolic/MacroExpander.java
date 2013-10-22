package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import java.util.ArrayList;
import java.util.Collection;


/**
 * Expands the macros in each rule of a definition.
 *
 * @author AndreiS
 */
public class MacroExpander extends TermTransformer {

    private final StepRewriter rewriter;

    public MacroExpander(Definition definition) {
        super(definition);
        rewriter = new StepRewriter(definition.macros(), definition);
    }

    public Definition processDefinition() {
        Definition processedDefinition = new Definition(definition.context());
        processedDefinition.addKLabelCollection(definition.kLabels());
        processedDefinition.addFrozenKLabelCollection(definition.frozenKLabels());
        for (Rule rule : definition.rules()) {
            processedDefinition.addRule(processRule(rule));
        }
        for (Rule rule : definition.functionRules().values()) {
            processedDefinition.addRule(processRule(rule));
        }
        processedDefinition.addRuleCollection(definition.macros());
        return processedDefinition;
    }

    public Rule processRule(Rule rule) {
        Term processedLeftHandSide = processTerm(rule.leftHandSide());
        Term processedRightHandSide = processTerm(rule.rightHandSide());
        Collection<Term> processedCondition = new ArrayList<Term>(rule.condition().size());
        for (Term conditionItem : rule.condition()) {
            processedCondition.add(processTerm(conditionItem));
        }
        UninterpretedConstraint processedLookups
                = (UninterpretedConstraint) rule.lookups().accept(this);
        return new Rule(
                processedLeftHandSide,
                processedRightHandSide,
                processedCondition,
                rule.freshVariables(),
                processedLookups,
                rule.getAttributes());
    }

    public Term processTerm(Term term) {
        return (Term) term.accept(this);
    }

    @Override
    protected Term transformTerm(Term term) {
        Term transformedTerm = rewriter.getOneSuccessor(term);
        return transformedTerm != null ? (Term) transformedTerm.accept(this) : term;
    }

}

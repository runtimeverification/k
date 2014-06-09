// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.Collection;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;


/**
 * Expands the macros in each rule of a definition and those in the initial
 * configuration.
 * 
 * @author AndreiS
 * 
 */
public class MacroExpander extends TermTransformer {

    private final StepRewriter rewriter;

    public MacroExpander(TermContext context) {
        super(context);
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
        for (Rule rule : definition.patternRules().values()) {
            processedDefinition.addRule(processRule(rule));
        }
        processedDefinition.addRuleCollection(definition.macros());
        return processedDefinition;
    }

    public Rule processRule(Rule rule) {
        Term processedLeftHandSide = processTerm(rule.leftHandSide());
        Term processedRightHandSide = processTerm(rule.rightHandSide());
        Collection<Term> processedRequires = new ArrayList<Term>(rule.requires().size());
        for (Term conditionItem : rule.requires()) {
            processedRequires.add(processTerm(conditionItem));
        }
        Collection<Term> processedEnsures = new ArrayList<Term>(rule.ensures().size());
        for (Term conditionItem : rule.ensures()) {
            processedEnsures.add(processTerm(conditionItem));
        }
        UninterpretedConstraint processedLookups
            = (UninterpretedConstraint) expandMacro(rule.lookups());
        return new Rule(
                rule.label(),
                processedLeftHandSide,
                processedRightHandSide,
                processedRequires,
                processedEnsures,
                rule.freshVariables(),
                processedLookups,
                rule.getAttributes(),
                definition);
    }

    public Term processTerm(Term term) {
        return (Term) expandMacro(term);
    }
    
    /**
     * Private helper method that keeps expanding macros in a specified node
     * until no macro is found.
     * 
     * @param node
     *            the specified node
     * @return the expanded node
     */
    private JavaSymbolicObject expandMacro(JavaSymbolicObject node) {
        JavaSymbolicObject expandedNode = (JavaSymbolicObject) node.accept(this);
        while (node != expandedNode) {
            node = expandedNode;
            expandedNode = (JavaSymbolicObject) node.accept(this);
        }

        return node;
    }

    @Override
    protected Term transformTerm(Term term) {
        Term transformedTerm = rewriter.getOneSuccessor(term);
        return transformedTerm != null ? transformedTerm : term;
    }

}

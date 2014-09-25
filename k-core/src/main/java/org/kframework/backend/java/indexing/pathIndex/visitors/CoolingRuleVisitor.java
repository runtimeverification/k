// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;

/**
 * Visitor for traversing cooling Rules
 * Author: OwolabiL
 * Date: 1/20/14
 * Time: 12:40 PM
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public class CoolingRuleVisitor extends RuleVisitor {
    private static final String K_RESULT_STRING = "KResult";
    private final Rule rule;
    private String currentLabel;
    private boolean isKItemHead = false;
    private static final String USER_LIST_REPLACEMENT = "UserList";

    public CoolingRuleVisitor(Rule rule, Context context) {
        super(context);
        this.rule = rule;
    }

    /**
     * In a cooling rule, indexing is done based on the first two elements in the KSequence.
     * There are two possibilities for the first element in the KSequence:
     *      1. It is a KItem which is also a KResult 'lvalue(_:KItem)
     *      2. It is a Variable of sort KItem
     * @param kSequence
     */
    @Override
    public void visit(KSequence kSequence) {
        Term term = kSequence.get(0);
        if (term instanceof KItem) {
            // This is case one of the head of the KSequence mentioned above. Set a flag to use in
            // distinguishing this case in the KItem visitor.
            isKItemHead = true;
        }
        term.accept(this);
        ((KItem) kSequence.get(1)).kLabel().accept(this);
    }

    /**
     * Visit the head of the KSequence and make an initial pString out of it
     * @param variable
     */
    @Override
    public void visit(Variable variable) {
        String requiredKResult = getRequiresKResultString(variable);
        String firstSort;
        //TODO(OwolabiL): Remove this check and use concrete sort instead
        if (rule.requires().toString().contains(requiredKResult)) {
            firstSort = K_RESULT_STRING;
        } else {
            //TODO(OwolabiL): use KEM instead?
            throw new IllegalStateException("First term in K cell is not a KResult: \n" + rule);
        }
        pString = pString.concat(firstSort + ".1.");
    }

    @Override
    public void visit(KLabelFreezer kLabelFreezer) {
        kLabelFreezer.term().accept(this);
    }

    /**
     * In visiting a KItem, we first visit its Label, and then visit its KList. However, we also
     * take care if the KItem is the first item in a KSequence.
     * @param kItem
     */
    @Override
    public void visit(KItem kItem) {
        visit((KLabelConstant) kItem.kLabel());
        if (isKItemHead) {
            Term term = ((KList) kItem.kList()).get(0);
            if (term instanceof Variable) {
                String requiredKResult = getRequiresKResultString(term);
                String firstSort;
                if (rule.requires().toString().contains(requiredKResult)) {
                    firstSort = K_RESULT_STRING;
                } else {
                    throw new IllegalStateException("First term in K cell is not a K result: \n" +
                            rule);
                }

                pStrings.add(pString + "1" + SEPARATOR + firstSort);
            }
        } else {
            visit((KList) kItem.kList());
        }
        this.proceed = false;
    }

    /**
     * Utility method. Used to check whether the rule requires a term to be a KResult.
     * TODO(OwolabiL): This is brittle. Check for a better way to fix this!!
     * @param term
     * @return
     */
    private String getRequiresKResultString(Term term) {
        return "isKResult(" + term + ")";
    }

    @Override
    public void visit(KLabelConstant kLabel) {
        currentLabel = kLabel.toString();
        pString = pString.concat(kLabel.toString() + ".");
    }

    @Override
    public void visit(KList kList) {
        Term frozenTerm;
        for (int i = 0; i < kList.concreteSize(); i++) {
            frozenTerm = kList.get(i);
            if (frozenTerm instanceof Hole) {
                pStrings.add(pString + (i + 1) + ".HOLE");
            } else {
                ArrayList<Production> productions =
                        (ArrayList<Production>) context.productionsOf(currentLabel);
                Production p = productions.get(0);
                if (productions.size() == 1) {
                    pStrings.add(pString + (i + 1) + SEPARATOR + p.getChildSort(0));
                } else {
                    //TODO(OwolabiL): this is not a good solution. what is needed is a way to know
                    // sort of each position in the list
                    pStrings.add(pString + (i + 1) + SEPARATOR + USER_LIST_REPLACEMENT);
                }
            }
        }
    }
}

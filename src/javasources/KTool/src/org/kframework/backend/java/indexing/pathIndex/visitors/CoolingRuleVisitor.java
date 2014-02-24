package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;

/**
 * Author: OwolabiL
 * Date: 1/20/14
 * Time: 12:40 PM
 */
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

    @Override
    public void visit(KSequence kSequence) {
        Term term = kSequence.get(0);
        if (term instanceof KItem) {
            isKItemHead = true;
        }
        term.accept(this);
        ((KItem) kSequence.get(1)).kLabel().accept(this);
    }

    @Override
    public void visit(Variable variable) {
        String requiredKResult = getRequiresKResultString(variable);
        String firstSort;
        //TODO(OwolabiL): Remove this check and use concrete sort instead
        if (rule.requires().toString().contains(requiredKResult)) {
            firstSort = K_RESULT_STRING;
        } else {
            throw new IllegalStateException("First term in K cell is not a K result: \n" + rule);
        }
        pString = pString.concat(firstSort + ".1.");
    }

    @Override
    public void visit(KLabelFreezer kLabelFreezer) {
        kLabelFreezer.term().accept(this);
    }

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
        for (int i = 0; i < kList.size(); i++) {
            frozenTerm = kList.get(i);
            //TODO(OwolabiL): remove instanceof!!
            if (frozenTerm instanceof Hole) {
                pStrings.add(pString + (i + 1) + ".HOLE");

            } else {
                ArrayList<Production> productions =
                        (ArrayList<Production>) context.productionsOf(currentLabel);
                Production p = productions.get(0);
                if (productions.size() == 1) {
                    pStrings.add(pString + (i + 1) + SEPARATOR + p.getChildSort(0));
                } else {
                    pStrings.add(pString + (i + 1) + SEPARATOR + USER_LIST_REPLACEMENT);
                }
            }
        }
    }
}

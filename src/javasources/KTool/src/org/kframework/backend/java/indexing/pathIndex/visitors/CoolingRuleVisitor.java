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
    private final Rule rule;
    private String currentLabel;


    public CoolingRuleVisitor(Rule rule, Context context) {
        super(context);
        this.rule = rule;
    }

    @Override
    public void visit(KSequence kSequence) {
        kSequence.get(0).accept(this);
        ((KItem) kSequence.get(1)).kLabel().accept(this);
    }

    //TODO(OwolabiL): This method can be greatly improved!
    @Override
    public void visit(Variable variable) {
        String requiredKResult = "isKResult(" + variable + ")";
        String firstSort;
        //TODO(OwolabiL): Remove this check and use concrete sort instead
        if (rule.requires().toString().contains(requiredKResult)) {
            firstSort = "KResult";
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
        visit((KLabelConstant)kItem.kLabel());
        visit((KList)kItem.kList());
        this.proceed = false;
    }

//    @Override
//    public void visit(KLabel kLabel) {
//        System.out.println("theKLabel: "+kLabel);
//        currentLabel = kLabel.toString();
//        pString = pString.concat(kLabel.toString() + ".");
//    }

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
                ArrayList<Production> productions = (ArrayList<Production>) context.productionsOf(currentLabel);
                Production p = productions.get(0);
                pStrings.add(pString + (i + 1) + SEPARATOR + p.getChildSort(i));
            }
        }
    }
}

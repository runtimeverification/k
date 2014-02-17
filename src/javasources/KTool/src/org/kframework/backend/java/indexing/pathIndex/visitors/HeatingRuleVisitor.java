package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.*;

/**
 * Author: OwolabiL
 * Date: 1/20/14
 * Time: 10:25 AM
 */
public class HeatingRuleVisitor extends RuleVisitor {
    private final Context context;
    private String currentLabel = null;
    private Stack<String> pStringStack;

    private int counter = 0;

    public HeatingRuleVisitor(Context context) {
        super(context);
        this.context = context;
        pStringStack = new Stack<>();
    }

    @Override
    public void visit(KSequence kSequence) {
        kSequence.get(0).accept(this);
    }

    @Override
    public void visit(KItem kItem) {
        visit((KLabelConstant)kItem.kLabel());
        visit((KList)kItem.kList());
    }

//    @Override
//    public void visit(KLabel kLabel) {
//        currentLabel = kLabel.toString();
//        if (pString.equals(START_STRING)) {
//            //we are at the initial pString
//            pString = pString.concat(kLabel.toString() + SEPARATOR);
//        } else {
//            //the original pString has been modified along the way
//            pString = pString.concat(counter + SEPARATOR + kLabel.toString() + SEPARATOR);
//        }
//    }

    @Override
    public void visit(KLabelConstant kLabel) {
        currentLabel = kLabel.toString();
        if (pString.equals(START_STRING)) {
            //we are at the initial pString
            pString = pString.concat(kLabel.toString() + SEPARATOR);
        } else {
            //the original pString has been modified along the way
            pString = pString.concat(counter + SEPARATOR + kLabel.toString() + SEPARATOR);
        }

        pStringStack.push(pString);
    }

    @Override
    public void visit(KList kList) {
        for (int i = 0; i < kList.size(); i++) {
            counter = i + 1;
            kList.get(i).accept(this);
        }
        pStringStack.pop();
//        this.proceed = false;
    }

    @Override
    public void visit(Variable variable) {
        String sort;
        ArrayList<Production> productions =
                (ArrayList<Production>) context.productionsOf(currentLabel);
        if (productions.size() == 1) {
            Production p = productions.get(0);
            sort = p.getChildSort(counter - 1);
            pStrings.add(pStringStack.peek() + counter + "." + sort);
        } else {
            if (productions.size() > 1) {
                //TODO(OwolabiL): find the exact sort of this variable before it was transformed
                // as part of this rule
                pStrings.add(pStringStack.peek() + counter + "." + "UserList");
            }
        }
    }
}

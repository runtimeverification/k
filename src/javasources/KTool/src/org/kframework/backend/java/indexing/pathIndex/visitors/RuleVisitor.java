package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.util.LookupCell;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

/**
 * Author: OwolabiL
 * Date: 1/20/14
 * Time: 1:50 PM
 */
public class RuleVisitor extends LocalVisitor {
    static final String SEPARATOR = ".";
    static final String START_STRING = "@.";
    private static final String EMPTY_K = "EMPTY_K";
    private static final String K_CELL_NAME = "k";
    final Context context;
    String pString;
    final List<String> pStrings;
    private boolean isKSequence = false;

    public RuleVisitor(Context context) {
        this.context = context;
        this.pString = START_STRING;
        this.pStrings = new ArrayList<>();
    }

    @Override
    public void visit(Rule rule) {
        visit(LookupCell.find(rule.leftHandSide(), K_CELL_NAME));
    }

    @Override
    public void visit(Cell cell) {
        cell.getContent().accept(this);
    }

    @Override
    public void visit(KSequence kSequence) {
        isKSequence = true;
        //taking care of .K
        if (kSequence.size() > 0) {
            kSequence.get(0).accept(this);
        } else if (kSequence.size() == 0) {
            //there may be more than one k cell in the rule and one of them may be empty e.g. the
            // join rule in IMP++, SIMPLE. The correct solution is to get pStrings from all kCells.
            pStrings.add(START_STRING + EMPTY_K);
        }
    }

    @Override
    public void visit(KItem kItem) {
        kItem.kLabel().accept(this);
        visit((KList) kItem.kList());
    }

    @Override
    public void visit(KLabelConstant kLabel) {
        pString = pString.concat(kLabel.toString());
    }

    @Override
    public void visit(KList kList) {
        String base = pString;
        if (kList.size() == 0) {
            pStrings.add(pString);
        }
        for (int i = 0; i < kList.size(); i++) {
            int position = i + 1;
            if (!isKSequence) {
                String pending = pString + SEPARATOR + (position);
                //TODO(OwolabiL): instanceof must be removed!
                if (kList.get(i) instanceof KItem) {
                    pStrings.add(pending + SEPARATOR + ((KItem) kList.get(i)).sort());
                } else {
                    pStrings.add(pending + SEPARATOR + ((Variable) kList.get(i)).sort());
                }
            } else {
                pString = base + SEPARATOR + position + SEPARATOR;
                kList.get(i).accept(this);
            }
        }
    }


    @Override
    public void visit(Variable variable) {
        pStrings.add(pString + variable.sort());

    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        pStrings.add(pString + uninterpretedToken.sort());
    }

    @Override
    public void visit(BoolToken boolToken) {
        pStrings.add(pString + boolToken.sort());
    }

    public List<String> getpStrings() {
        return pStrings;
    }
}
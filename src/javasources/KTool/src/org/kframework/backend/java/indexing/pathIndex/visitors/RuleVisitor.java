package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.indexing.util.MultipleCellUtil;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.util.LookupCell;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.List;

/**
 * Author: OwolabiL
 * Date: 1/20/14
 * Time: 1:50 PM
 */
public class RuleVisitor extends LocalVisitor {
    static final String SEPARATOR = ".";
    static final String START_STRING = "@.";
    final Context context;
    String pString;
    List<String> pStrings;
    private boolean isKSequence = false;

    public RuleVisitor(Context context) {
        this.context = context;
        this.pString = START_STRING;
        this.pStrings = new ArrayList<>();
    }

    @Override
    public void visit(Rule rule) {
        visit(LookupCell.find(rule.leftHandSide(), "k"));
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
        }

        //else if (kSequence.size() == 0) {
            //TODO(OwolabiL): there may be more than one k cell in the rule and one of them may be
            // empty e.g. the join rule in IMP++. The correct solution is to get pStrings from all
            // kCells.
        //}
    }

    @Override
    public void visit(KItem kItem) {
        visit((KLabelConstant)kItem.kLabel());
        visit((KList)kItem.kList());
    }

//    @Override
//    public void visit(KLabel kLabel) {
//        pString = pString.concat(kLabel.toString());
//    }

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
    public void visit(BoolToken boolToken) {
        pStrings.add(pString + boolToken.sort());
    }

    public List<String> getpStrings() {
        return pStrings;
    }
}
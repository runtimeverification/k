// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.util.LookupCell;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.List;

/** This Visitor class traverses a rule and makes PStrings out of the rule using
 *  the contents of the k cell
 *
 * Author: OwolabiL
 * Date: 1/20/14
 * Time: 1:50 PM
 *
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public class RuleVisitor extends LocalVisitor {
    static final String SEPARATOR = ".";
    static final String START_STRING = "@.";
    private static final String EMPTY_K = "EMPTY_K";
    private static final String K_CELL_NAME = "k";
    public static final String NO_K_CELL_PSTRING = "@.NO_K_CELL";
    final Context context;
    String pString;
    final List<String> pStrings;
    private boolean isKSequence = false;

    public boolean isHasNOKCellRule() {
        return hasNOKCellRule;
    }

    private boolean hasNOKCellRule;

    public RuleVisitor(Context context) {
        this.context = context;
        this.pString = START_STRING;
        this.pStrings = new ArrayList<>();
    }

    @Override
    public void visit(Rule rule) {
        Cell kCell = LookupCell.find(rule.leftHandSide(), K_CELL_NAME);
        if (kCell != null){
            visit(kCell);
        }else{
            if(!hasNOKCellRule){
                hasNOKCellRule = true;
            }
            pStrings.add(NO_K_CELL_PSTRING);
        }
    }

    @Override
    public void visit(Cell cell) {
        if (cell.getLabel().equals(K_CELL_NAME)){
            cell.getContent().accept(this);
        } else if(cell.contentKind() == Kind.CELL_COLLECTION){
            super.visit(cell);
        }
    }

    @Override
    public void visit(KSequence kSequence) {
        isKSequence = true;
        //taking care of .K
        if (kSequence.size() > 0) {
            //needed for env rule in fun
            if (kSequence.size() > 1){
                kSequence.get(0).accept(this);
                kSequence.get(1).accept(this);
            } else{
                kSequence.get(0).accept(this);
            }
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
    public void visit(KLabelInjection kLabelInjection) {
        pString = pString.concat(kLabelInjection.term().kind().toString());
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
                    pStrings.add(pending + SEPARATOR + (kList.get(i)).sort());
                } else {
                    pStrings.add(pending + SEPARATOR + (kList.get(i)).sort());
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
// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddPathConditionToReachabilityKRule extends CopyOnWriteTransformer {

    public AddPathConditionToReachabilityKRule(Context context) {
        super("Add path condition to reachability rule represented as K rule", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {

        if (!node.containsAttribute(ReachabilityRuleToKRule.RL_ATR)) {
            return node;
        }

        if (node.getBody() instanceof Rewrite) {
            Rewrite body = (Rewrite) node.getBody();

            Term lcfg = body.getLeft().shallowCopy();
            Term rcfg = body.getRight().shallowCopy();

            //TODO: handle ensures
            Term condition = node.getRequires();
            if (condition instanceof KApp) {
                KApp appCondition = (KApp) condition;

                EliminateRRWrapper errw = new EliminateRRWrapper(context);
                Term newCond = (Term) errw.visitNode(appCondition);

                Term lphi = errw.getLphi();
                Term rphi = errw.getRphi();

                Variable pc = Variable.getFreshVar("K");
                Term leftBag = addPathCondition(lcfg, pc);

                List<Term> pcAndPhi = new ArrayList<Term>();
                pcAndPhi.add(pc);
                pcAndPhi.add(rphi);
                Term pcNew = new KApp(KLabelConstant.BOOL_ANDBOOL_KLABEL, new KList(pcAndPhi));
                Term rightBag = addPathCondition(rcfg, pcNew);

//                KApp unsat = StringBuiltin.kAppOf("unsat");
//                KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, pc, KApp.of(KLabelConstant.NOTBOOL_KLABEL, lphi)));
                KApp sat = StringBuiltin.kAppOf("sat");
                KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, pc, lphi));
                Term newCondition = KApp.of(KLabelConstant.KEQ_KLABEL, checkSat, sat);
                newCondition = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, newCondition, newCond);

                Sentence rule = new Sentence();
                rule.setBody(new Rewrite(leftBag, rightBag, context));
                Rule newRule = new Rule(rule);
                newRule.setRequires(newCondition);
                newRule.setAttributes(node.getAttributes().shallowCopy());
                return newRule;
            }
        }

        return node;
    }

    private Term addPathCondition(Term cfg, Term pcContent) {

        // create lhs path condition cell
        Cell pcCell = new Cell();
        pcCell.setLabel(MetaK.Constants.pathCondition);
        pcCell.setEllipses(Ellipses.NONE);
        pcCell.setContents(pcContent);

        return AddConditionToConfig.addSubcellToCell((Cell)cfg, pcCell);
    }
}

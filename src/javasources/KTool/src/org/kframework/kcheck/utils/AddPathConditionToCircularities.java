// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.backend.symbolic.AddConditionToConfig;
import org.kframework.backend.symbolic.AddPathCondition;
import org.kframework.compile.utils.MetaK;
import org.kframework.kcheck.RLBackend;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddPathConditionToCircularities extends CopyOnWriteTransformer {

    public AddPathConditionToCircularities(Context context, List<ASTNode> reachabilityRules) {
        super("Add path condition to circularities", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {

        if(node.getAttribute(AddCircularityRules.RRULE_ATTR) != null && (node.getBody() instanceof Rewrite)) {


            //TODO:  use ensures to get phi'

            // extract phi and phi'
            Term cnd = node.getRequires();
            ExtractPatternless ep = new ExtractPatternless(context, false);
            cnd = (Term) ep.visitNode(cnd);

            // separate left and right
            Rewrite ruleBody = (Rewrite) node.getBody();
            Term left = ruleBody.getLeft().shallowCopy();
            Term right = ruleBody.getRight().shallowCopy();


            // create lhs path condition cell
            Variable psi = Variable.getFreshVar(Sort.K);
            Cell leftCell = new Cell();
            leftCell.setLabel(MetaK.Constants.pathCondition);
            leftCell.setEllipses(Ellipses.NONE);
            leftCell.setContents(psi);
            left = AddConditionToConfig.addSubcellToCell((Cell)left, leftCell);

            // create rhs path condition cell
            Cell rightCell = new Cell();
            rightCell.setLabel(MetaK.Constants.pathCondition);
            rightCell.setEllipses(Ellipses.NONE);
            rightCell.setContents(KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, psi, ep.getPhi()), ep.getPhiPrime()));
            right = AddConditionToConfig.addSubcellToCell((Cell)right, rightCell);

            // condition
//            Term implication = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, psi, KApp.of(KLabelConstant.NOTBOOL_KLABEL, ep.getPhi()));
//            KApp unsat = StringBuiltin.kAppOf("unsat");
//            KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), implication);
//            implication = KApp.of(KLabelConstant.KEQ_KLABEL, checkSat, unsat);
            Term pc = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, psi, ep.getPhi()), ep.getPhiPrime());
            pc = AddPathCondition.checkSat(pc, context);

            Rule newRule = new Rule(left, right, context);
            Term cc = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, cnd, pc);
            if (RLBackend.SIMPLIFY) {
                cc = KApp.of(KLabelConstant.of(RLBackend.SIMPLIFY_KLABEL, context) , cc);
            }
            newRule.setRequires(cc);
            newRule.setAttributes(node.getAttributes().shallowCopy());
            return newRule;
        }

        return super.visit(node, _);
    }
}

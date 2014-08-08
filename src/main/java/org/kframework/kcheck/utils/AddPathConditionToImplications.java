// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.symbolic.AddConditionToConfig;
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
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddPathConditionToImplications extends CopyOnWriteTransformer {


    private List<ASTNode> reachabilityRules;

    public AddPathConditionToImplications(Context context, List<ASTNode> reachabilityRules) {
        super("Add path condition to implication rules", context);
        this.reachabilityRules = reachabilityRules;
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if(node.getAttribute(AddImplicationRules.IMPLRULE_ATTR) != null && (node.getBody() instanceof Rewrite)) {

            // get the corresponding reachability rule
            int rIndex = Integer.parseInt(node.getAttribute(AddImplicationRules.IMPLRULE_ATTR));
            ASTNode rrule = reachabilityRules.get(rIndex);
            ReachabilityRuleKILParser parser = new ReachabilityRuleKILParser(context);
            parser.visitNode(rrule);

            VariablesVisitor vvpi = new VariablesVisitor(context);
            vvpi.visitNode(parser.getPi());
            VariablesVisitor vvpiprime = new VariablesVisitor(context);
            vvpiprime.visitNode(parser.getPi_prime());
            List<Variable> fresh = new ArrayList<Variable>();
            for(Variable v : vvpi.getVariables()) {
                if (!AddCircularityRules.varInList(v, vvpiprime.getVariables())) {
                    fresh.add(v);
                }
            }

            //TODO:  use ensures to get phi'

            // extract phi and phi'
            Term cnd = node.getRequires();
            ExtractPatternless ep = new ExtractPatternless(context, true);
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
//            rightCell.setContents(KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, psi, ep.getPhiPrime()));
            rightCell.setContents(psi);
            right = AddConditionToConfig.addSubcellToCell((Cell)right, rightCell);

            // condition
            Term implication = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, psi, KApp.of(KLabelConstant.NOTBOOL_KLABEL, ep.getPhiPrime()));
            KApp unsat = StringBuiltin.kAppOf("unsat");
            KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), implication);
            implication = KApp.of(KLabelConstant.KEQ_KLABEL, checkSat, unsat);

            // return new rule
            Rule newRule = new Rule(left, right, context);
            Term cc = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, cnd.shallowCopy(), implication);
            if (RLBackend.SIMPLIFY) {
                cc = KApp.of(KLabelConstant.of(RLBackend.SIMPLIFY_KLABEL, context) , cc);
            }
            newRule.setRequires(cc);
            newRule.setAttributes(node.getAttributes().shallowCopy());
            newRule = (Rule) new MakeFreshVariables(context, fresh).visitNode(newRule);

            return newRule;
        }

        return super.visit(node, _);
    }
}

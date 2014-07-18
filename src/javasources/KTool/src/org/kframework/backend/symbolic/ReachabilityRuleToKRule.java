// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class ReachabilityRuleToKRule extends CopyOnWriteTransformer {

    private final String ML_SORT = "MLFormula";
    private final String ML_AND_KLABEL = "'_/\\ML_";
    public static final String RL_ATR = "reachability-formula";
    public static final String RR_COND = "'RRCondition(_,_,_)";

    public ReachabilityRuleToKRule(Context context) {
        super("Transform reachability rule into K rule with RRCondition as constructor",
                context);
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if (!node.containsAttribute(RL_ATR)) {
            return node;
        }

        if (node.getBody() instanceof Rewrite) {
            Rewrite body = (Rewrite) node.getBody();

            Term left = body.getLeft().shallowCopy();
            Term right = body.getRight().shallowCopy();

            if (left.getSort().equals(ML_SORT)
                    && right.getSort().equals(ML_SORT)) {
                TermCons ltc = (TermCons) left;
                TermCons rtc = (TermCons) right;
                Term ruleCond = node.getRequires().shallowCopy();
                if (ltc.getProduction().getKLabel().equals(ML_AND_KLABEL)
                        && ltc.getProduction().getKLabel()
                                .equals(ML_AND_KLABEL)) {

                    // process left
                    Term lcfg = ltc.getContents().get(0).shallowCopy();
                    Term lphi = ltc.getContents().get(1).shallowCopy();

                    // process right
                    Term rcfg = rtc.getContents().get(0).shallowCopy();
                    Term rphi = rtc.getContents().get(1).shallowCopy();

                    Sentence rule = new Sentence();
                    rule.setBody(new Rewrite(lcfg, rcfg, context));

                    if(ruleCond != null) {
                        rule.setRequires(KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, KApp.of(KLabelConstant.of(RR_COND), lphi, rphi), ruleCond));
                    }
                    else {
                        rule.setRequires(KApp.of(KLabelConstant.of(RR_COND), lphi, rphi));
                    }
                    Rule newRule = new Rule(rule);
                    newRule.setAttributes(node.getAttributes().shallowCopy());
//                    System.out.println(newRule);
                    return newRule;
                }
            }

        }

        return node;
    }
}

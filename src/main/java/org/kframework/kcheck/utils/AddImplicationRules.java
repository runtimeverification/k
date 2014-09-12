// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.kcheck.RLBackend;
import org.kframework.kil.ASTNode;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddImplicationRules extends CopyOnWriteTransformer {

    public static final String IMPLRULE_ATTR = "implication-rule";
    private List<ASTNode> reachabilityRules;

    public AddImplicationRules(Context context, List<ASTNode> reachabilityRules) {
        super("Add rules for implication", context);
        this.reachabilityRules = reachabilityRules;
    }

    @Override
    public ASTNode visit(Module node, Void _)  {

        List<ModuleItem> items = node.getItems();
        node = node.shallowCopy();
        node.setItems(items);


        for (ASTNode rr : reachabilityRules) {
            if (rr instanceof Sentence) {
                Sentence r = (Sentence) rr;

                ReachabilityRuleKILParser parser = new ReachabilityRuleKILParser(
                        context);
                parser.visitNode(r);


                Term newPi = parser.getPi_prime().shallowCopy();
                Term implies = AddCheckConstants.getFreshImplicationForRule(reachabilityRules.indexOf(rr), context);
                SetCellContent app = new SetCellContent(context, implies, "k");
                newPi = (Term) app.visitNode(newPi);


                Term newPiPrime = parser.getPi_prime().shallowCopy();
                SetCellContent appPrime = new SetCellContent(context, KSequence.EMPTY, "k");
                newPiPrime = (Term) appPrime.visitNode(newPiPrime);

                // insert patternless formulas into condition
                Term phi = parser.getPhi().shallowCopy();
                Term phiPrime = parser.getPhi_prime().shallowCopy();
                Term rrcond = KApp.of(KLabelConstant.of(RLBackend.INTERNAL_KLABEL, context), phi, phiPrime);

                Term condition = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, rrcond, BoolBuiltin.TRUE);

                Rule implicationRule = new Rule(newPi, newPiPrime, context);
                implicationRule.setRequires(condition);
                int correspondingIndex = reachabilityRules.indexOf(rr);
                implicationRule.addAttribute(IMPLRULE_ATTR, correspondingIndex + "");

                items.add(implicationRule);
            }
        }

        return node;
    }
}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Replace each (data) constant with a symbolic value
 * and add an equality in the side condition of the rule.
 *
 * @author andreiarusoaie
 */
public class ReplaceConstants extends CopyOnWriteTransformer {

    public ReplaceConstants(Context context) {
        super("Replace Constants with Variables", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if (!node.containsAttribute(SymbolicBackend.SYMBOLIC)) {
            return node;
        }

        if (node.getBody() instanceof Rewrite) {
            ConstantsReplaceTransformer crt = new ConstantsReplaceTransformer(
                    "", context);
            Rewrite rew = (Rewrite) node.getBody();
            Term left = rew.getLeft().shallowCopy();
//            System.out.println("LEFT : " + node);
            rew.setLeft((Term) crt.visitNode(left), context);
            Map<Variable, KApp> newGeneratedSV = crt.getGeneratedSV();
            Term condition = node.getRequires();

            List<Term> terms = new ArrayList<Term>();
            for (Entry<Variable, KApp> entry : newGeneratedSV.entrySet()) {
                List<Term> vars = new ArrayList<Term>();
                vars.add(entry.getKey());
//                vars.add(KApp.of(new KInjectedLabel(entry.getValue())));
                vars.add(entry.getValue());
                terms.add(new KApp(KLabelConstant.of(KLabelConstant.KEQ.getLabel(), context), new KList(vars)));

                Token token = (Token) (entry.getValue().getLabel());
                terms.add(KApp.of(
                        KLabelConstant.of(AddPredicates.predicate(
                                token.tokenSort().replaceFirst("#", "")), context),
                        entry.getKey()));
            }

            if (terms.isEmpty())
                return node;

            Term newCondition = new KApp(KLabelConstant.ANDBOOL_KLABEL, new KList(
                    terms));

            if (condition != null) {
                List<Term> vars = new ArrayList<Term>();
                vars.add(condition);
                vars.add(newCondition);
                newCondition = new KApp(KLabelConstant.ANDBOOL_KLABEL,
                        new KList(vars));
            }

            node = node.shallowCopy();
            node.setBody(rew);
            node.setRequires(newCondition);
        }
//        System.out.println("LEFT': " + node);
//        System.out.println("\n\n");

        return node;
    }
}

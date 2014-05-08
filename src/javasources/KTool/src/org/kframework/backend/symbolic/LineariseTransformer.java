// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Replace each variable X in the left hand side with a new one Y
 * of the same sort and add the equality X == Y in the path condition.
 *
 * @author andreiarusoaie
 */
public class LineariseTransformer extends CopyOnWriteTransformer {

    public LineariseTransformer(Context context) {
        super("Linearise Rules", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if (!node.containsAttribute(SymbolicBackend.SYMBOLIC)) {
            return node;
        }


        if (node.getBody() instanceof Rewrite) {
            VariableReplaceTransformer vrt = new VariableReplaceTransformer(context);
            Rewrite rew = (Rewrite) node.getBody();
            Term transformedLeft = rew.getLeft();
            transformedLeft = (Term) vrt.visitNode(transformedLeft);
            rew.shallowCopy();
            rew.setLeft(transformedLeft, context);

            Map<Variable, Variable> newGeneratedSV = vrt.getGeneratedVariables();
            Term condition = node.getRequires();

            List<Term> terms = new ArrayList<Term>();
            for (Entry<Variable, Variable> entry : newGeneratedSV.entrySet()) {
                List<Term> vars = new ArrayList<Term>();
                vars.add(entry.getKey());
                vars.add(entry.getValue());
                terms.add(new KApp(KLabelConstant.of(KLabelConstant.KEQ.getLabel(), context), new KList(vars)));
            }

            if (terms.isEmpty())
                return node;

            Term newCondition = new KApp(KLabelConstant.ANDBOOL_KLABEL,
                    new KList(terms));

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
        return node;
    }
}

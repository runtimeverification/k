// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * Initially created by Traian Florin Serbanuta
 * Date: 10/31/12
 * Time: 11:46 PM
 */
public class ContextsToHeating extends CopyOnWriteTransformer {
    private List<ModuleItem> rules = new ArrayList<ModuleItem>();

    public ContextsToHeating(Context context) {
           super("Contexts to Heating Rules", context);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        return ((Module)super.visit(node, _)).addModuleItems(rules);
    }

    /* assumes term has exactly one rewrite and returns the list
     * C[v], v, t1, t2 such that
     * v is a fresh variable and term = C[t1 => t2] */
    private List<Term> splitRewrite(Term term)  {
        final Variable v;
        v = Variable.getAnonVar(Sort.KITEM);
        final List<Term> list = new ArrayList<Term>();
        CopyOnWriteTransformer transformer = new CopyOnWriteTransformer("splitter", context) {
            @Override public ASTNode visit(Rewrite rewrite, Void _) {
                list.add(rewrite.getLeft());
                list.add(rewrite.getRight());
                return v;
            }
        };
        Term result = (Term) transformer.visitNode(term);
        list.add(0, v);
        list.add(0, result);
        return list;
    }

    private Term substituteHole(Term term, Term replacement)  {
        return substituteSubstitutable(term, Hole.KITEM_HOLE, replacement);
    }

    public Term freeze(Term term) {
        return new Freezer(substituteHole(term, new FreezerHole(0)));
    }

    private Term substituteVariable(Term term, Variable variable, Term replacement)  {
        return substituteSubstitutable(term, variable, replacement);
   }

    private Term substituteSubstitutable(Term term, Term variable, Term replacement)  {
        HashMap<Term, Term> hashMap = new HashMap<Term, Term>();
        hashMap.put(variable, replacement);
        Substitution substitution = new Substitution(hashMap, context);
        if (term == null) {
            return null;
        }
        return (Term) substitution.visitNode(term);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        Term body = (Term) new ResolveAnonymousVariables(context).visitNode(node.getBody());
        int countHoles = MetaK.countHoles(body, context);
        if (countHoles == 0) {
            throw KExceptionManager.criticalError(
                            "Contexts must have at least one HOLE.",
                            this, node);
        }
        Integer countRewrites = MetaK.countRewrites(body, context);
        if (countRewrites > 1) {
            throw KExceptionManager.criticalError(
                            "Contexts can contain at most one rewrite",
                            this, node);
        } else if (countRewrites == 0) {
            body = substituteHole(body, new Rewrite(Hole.KITEM_HOLE, Hole.KITEM_HOLE, context));
        }
        List<Term> r = splitRewrite(body);
        Term rewriteContext = r.get(0);
        Variable freshVariable = (Variable)r.get(1);
        Term left = r.get(2);
        Term right = r.get(3);
        if (!(left instanceof Hole)) {
            throw KExceptionManager.criticalError(
                            "Only the HOLE can be rewritten in a context definition",
                            this, node);
        }
        Term lhsHeat = rewriteContext;
        List<Term> rewriteList = new ArrayList<Term>();
        rewriteList.add(substituteHole(right, freshVariable));
        rewriteList.add(new Freezer(substituteVariable(rewriteContext, freshVariable, new FreezerHole(0))));
        Term rhsHeat = new KSequence(rewriteList);
        Rule heatingRule = new Rule(lhsHeat, rhsHeat, context);
        heatingRule.setRequires(substituteHole(node.getRequires(), freshVariable));
        heatingRule.setEnsures(substituteHole(node.getEnsures(), freshVariable));
        heatingRule.getAttributes().putAll(node.getAttributes());
        heatingRule.setLocation(node.getLocation());
        heatingRule.setSource(node.getSource());
        heatingRule.putAttribute(MetaK.Constants.heatingTag,"");
        rules.add(heatingRule);

        Rule coolingRule = new Rule(rhsHeat, lhsHeat, context);
        coolingRule.getAttributes().putAll(node.getAttributes());
        coolingRule.setLocation(node.getLocation());
        coolingRule.setSource(node.getSource());
        coolingRule.putAttribute(MetaK.Constants.coolingTag,"");
        rules.add(coolingRule);

        return null;
    }

    @Override
    public ASTNode visit(Syntax node, Void _) {
        return node;
    }

    @Override
    public ASTNode visit(Rule node, Void _) {
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _) {
        return node;
    }
}

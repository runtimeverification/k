// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Filter the rule side condition such that it contains only
 * SMTLIB translatable items. The filtered terms are stored
 * in a list for further use.
 *
 * @author andreiarusoaie
 */
public class ConditionTransformer extends CopyOnWriteTransformer {

    List<Term> filteredTerms = new ArrayList<Term>();
    List<Term> generatedPredicates = new ArrayList<>();

    public ConditionTransformer(Context context) {
        super("Filter side conditions", context);
    }

    @Override
    public ASTNode visit(KApp node, Void _)  {
        Term label = node.getLabel();
        if (label instanceof KLabelConstant) {
            Term content = node.getChild();
            if (label.equals(KLabelConstant.ANDBOOL_KLABEL)) {
                if (content instanceof KList) {
                    List<Term> terms = ((KList) content).getContents();
                    List<Term> remainingTerms = new ArrayList<Term>();
                    for (Term t : terms) {
                        CheckSmtLibByAddingPredicates csv = new CheckSmtLibByAddingPredicates(context);
                        csv.visitNode(t);
                        if (csv.smtValid()) {
                            filteredTerms.add(t.shallowCopy());
                            generatedPredicates.addAll(csv.getContents());
                        }
                        else remainingTerms.add(t.shallowCopy());
                    }
                    content = new KList(remainingTerms);
                }
            } else {
                CheckSmtLibByAddingPredicates csv = new CheckSmtLibByAddingPredicates(context);
                csv.visitNode(content);
                if (csv.smtValid()) {
                    filteredTerms.add(content.shallowCopy());
                    generatedPredicates.addAll(csv.getContents());
                    content = new KList();
                }
            }

            node = node.shallowCopy();
            node.setChild(content);
            return node;
        }

        return super.visit(node, _);
    }

    public List<Term> getFilteredTerms() {
        return filteredTerms;
    }

    public List<Term> getGeneratedPredicates() {
        return generatedPredicates;
    }
}

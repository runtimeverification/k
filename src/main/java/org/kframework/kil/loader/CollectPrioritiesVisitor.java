// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Definition;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityBlockExtended;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.SDFHelper;

public class CollectPrioritiesVisitor extends BasicVisitor {

    public CollectPrioritiesVisitor(Context context) {
        super(context);
    }

    public Void visit(Definition def, Void _) {
        super.visit(def, _);
        context.finalizePriority();
        return null;
    }

    public Void visit(Syntax node, Void _) {
        // collect left and right associativity
        for (int i = 0; i < node.getPriorityBlocks().size() - 1; i++) {
            PriorityBlock pb1 = node.getPriorityBlocks().get(i);
            PriorityBlock pb2 = node.getPriorityBlocks().get(i + 1);
            for (Production prd1 : pb1.getProductions()) {
                // allow priorities only between productions that have a sort at the left or right
                if (prd1.isSyntacticSubsort() || prd1.isConstant())
                    continue;
                if (!(prd1.getItems().get(0) instanceof NonTerminal) && !(prd1.getItems().get(prd1.getItems().size() - 1) instanceof NonTerminal))
                    continue;
                for (Production prd2 : pb2.getProductions()) {
                    if (prd2.isSyntacticSubsort() || prd2.isConstant())
                        continue;
                    if (!(prd2.getItems().get(0) instanceof NonTerminal) && !(prd2.getItems().get(prd2.getItems().size() - 1) instanceof NonTerminal))
                        continue;
                    context.addPriority(prd1.getKLabel(), prd2.getKLabel());
                }
            }
        }

        // collect left and right associativity
        for (PriorityBlock pb1 : node.getPriorityBlocks()) {
            manageAssociativity(new HashSet<Production>(pb1.getProductions()), pb1.getAssoc());
        }
        return null;
    }

    public Void visit(PriorityExtended node, Void _) {
        for (int i = 0; i < node.getPriorityBlocks().size() - 1; i++) {
            PriorityBlockExtended pb1 = node.getPriorityBlocks().get(i);
            PriorityBlockExtended pb2 = node.getPriorityBlocks().get(i + 1);
            // example: syntax priorities tag1 > tag2
            for (KLabelConstant prd1 : pb1.getProductions()) {
                // get all the productions annotated with tag1
                Set<Production> prods1 = SDFHelper.getProductionsForTag(prd1.getLabel(), context);
                for (KLabelConstant prd2 : pb2.getProductions()) {
                    // get all the productions annotated with tag2
                    Set<Production> prods2 = SDFHelper.getProductionsForTag(prd2.getLabel(), context);
                    // add all the relations between all the productions annotated with tag1 and tag 2
                    for (Production p1 : prods1) {
                        if (p1.isSubsort())
                            continue;
                        for (Production p2 : prods2) {
                            if (p2.isSubsort())
                                continue;
                            context.addPriority(p1.getKLabel(), p2.getKLabel());
                        }
                    }
                }
            }
        }
        return null;
    }

    public Void visit(PriorityExtendedAssoc node, Void _) {
        Set<Production> prods = new HashSet<>();
        for (KLabelConstant label : node.getChildren(null))
            prods.addAll(SDFHelper.getProductionsForTag(label.getLabel(), context));

        manageAssociativity(prods, node.getAssoc());
        return null;
    }

    public void manageAssociativity(Set<Production> prods, String assoc) {
        for (Production p1 : prods) {
            if (p1.getKLabel() != null) {
                for (Production p2 : prods) {
                    // collect the associativity for the entire block (production1 to production2)
                    if (p1 != p2) {
                        if (assoc.equals(Constants.LEFT) || assoc.equals(Constants.NON_ASSOC))
                            context.addLeftAssoc(p1.getKLabel(), p2.getKLabel());
                        if (assoc.equals(Constants.RIGHT) || assoc.equals(Constants.NON_ASSOC))
                            context.addRightAssoc(p1.getKLabel(), p2.getKLabel());
                    }
                }
                // collect the associativity for the production with itself
                if (p1.containsAttribute(Constants.LEFT) || p1.containsAttribute(Constants.NON_ASSOC))
                    context.addLeftAssoc(p1.getKLabel(), p1.getKLabel());
                if (p1.containsAttribute(Constants.RIGHT) || p1.containsAttribute(Constants.NON_ASSOC))
                    context.addRightAssoc(p1.getKLabel(), p1.getKLabel());
            }
        }
    }
}

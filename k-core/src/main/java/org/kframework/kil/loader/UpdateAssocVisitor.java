// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import java.util.Set;

import org.kframework.kil.KLabelConstant;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.SDFHelper;

public class UpdateAssocVisitor extends BasicVisitor {
    public UpdateAssocVisitor(Context context) {
        super(context);
    }

    /**
     * Because the block associativity is not reflexive in SDF, I have to add it manually.
     */
    @Override
    public Void visit(PriorityExtendedAssoc pri, Void _) {
        for (KLabelConstant c : pri.getTags()) {
            Set<Production> prods = SDFHelper.getProductionsForTag(c.getLabel(), context);
            for (Production p : prods) {
                if (!p.containsAttribute(Constants.LEFT) &&
                    !p.containsAttribute(Constants.RIGHT) &&
                    !p.containsAttribute(Constants.NON_ASSOC)) {
                    p.addAttribute(pri.getAssoc(), "");
                }
            }
        }
        return null;
    }

    @Override
    public Void visit(PriorityBlock pri, Void _) {
        if (!pri.getAssoc().equals("")) {
            for (Production p : pri.getProductions()) {
                if (!p.containsAttribute(Constants.LEFT) &&
                    !p.containsAttribute(Constants.RIGHT) &&
                    !p.containsAttribute(Constants.NON_ASSOC)) {
                    p.addAttribute(pri.getAssoc(), "");
                }
            }
        }
        return null;
    }
}

// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.*;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/19/12
 * Time: 10:24 PM
 */
public class AddSupercoolDefinition extends CopyOnWriteTransformer {
    private List<Rule> superCools = new ArrayList<Rule>();

    public AddSupercoolDefinition(Context context) {
        super("AddSupercoolDefinition", context);
    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
        superCools.clear();
        node = (Module) super.visit(node, _void);
        if (!superCools.isEmpty()) {
            node = node.shallowCopy();
            node.setItems(new ArrayList<ModuleItem>(node.getItems()));
            node.getItems().addAll(superCools);
        }
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _void)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _void)  {
        return node;
    }

    @Override
    public ASTNode visit(Rule node, Void _void)  {
        if (!node.containsAttribute(MetaK.Constants.coolingTag)) {
            return node;
        }
        if (!(node.getBody() instanceof  Rewrite)) {
            throw KExceptionManager.criticalError(
                            "Cooling rules should have rewrite at the top.",
                            this, node);
        }
        KSequence kSequence;
        Rewrite rewrite = (Rewrite) node.getBody();
        if (!(rewrite.getLeft() instanceof KSequence)) {
            throw KExceptionManager.criticalError(
                            "Cooling rules should have a K sequence in the lhs.",
                            this, node);
        }
        kSequence = (KSequence) rewrite.getLeft();
        java.util.List<Term> kSequenceContents = kSequence.getContents();
        if (kSequenceContents.size() != 2 ) {
            throw KExceptionManager.criticalError(
                            "Heating/Cooling rules should have exactly 2 items in their K Sequence.",
                                this, node);
        }
        rewrite = rewrite.shallowCopy();
        KSequence left = new KSequence();
        left.add(rewrite.getLeft());
        Variable fresh = Variable.getAnonVar(Sort.K);
        left.add(fresh);
        KSequence right = new KSequence();
        right.add(rewrite.getRight());
        right.add(fresh);
        rewrite.replaceChildren(
                KApp.of(KLabelConstant.COOL_KLABEL, left),
                KApp.of(KLabelConstant.COOL_KLABEL, right),
                context);
        Rule superCoolNode = node.shallowCopy();
        superCoolNode.removeAttribute("cool");

        superCoolNode.setBody(rewrite);
        superCools.add(superCoolNode);
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _void)  {
        return node;
    }
}

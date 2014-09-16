// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;
import java.util.List;

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
    public ASTNode visit(Module node, Void _)  {
        superCools.clear();
        node = (Module) super.visit(node, _);
        if (!superCools.isEmpty()) {
            node = node.shallowCopy();
            node.setItems(new ArrayList<ModuleItem>(node.getItems()));
            node.getItems().addAll(superCools);
        }
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if (!node.containsAttribute(MetaK.Constants.coolingTag)) {
            return node;
        }
        if (!(node.getBody() instanceof  Rewrite)) {
            GlobalSettings.kem.registerCriticalError(
                            "Cooling rules should have rewrite at the top.",
                            this, node);
        }
        KSequence kSequence;
        Rewrite rewrite = (Rewrite) node.getBody();
        if (!(rewrite.getLeft() instanceof KSequence)) {
            GlobalSettings.kem.registerCriticalError(
                            "Cooling rules should have a K sequence in the lhs.",
                            this, node);
        }
        kSequence = (KSequence) rewrite.getLeft();
        java.util.List<Term> kSequenceContents = kSequence.getContents();
        if (kSequenceContents.size() != 2 ) {
            GlobalSettings.kem.registerCriticalError(
                            "Heating/Cooling rules should have exactly 2 items in their K Sequence.",
                                this, node);
        }
        final Term cool = kSequenceContents.get(0);
        kSequenceContents = new ArrayList<Term>(kSequenceContents);
        kSequenceContents.set(0, KApp.of(KLabelConstant.COOL_KLABEL, cool));
        kSequence = kSequence.shallowCopy();
        kSequence.setContents(kSequenceContents);
        rewrite = rewrite.shallowCopy();
        rewrite.replaceChildren(
                kSequence,
                KApp.of(KLabelConstant.COOL_KLABEL, rewrite.getRight()),
                context);
        Rule superCoolNode = node.shallowCopy();
        superCoolNode.removeAttribute("cool");

        superCoolNode.setBody(rewrite);
        superCools.add(superCoolNode);
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }
}

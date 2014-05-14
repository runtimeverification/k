// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.StringUtil;

import java.util.ArrayList;

/**
 * Define KLabel2String and String2KLabel
 */
public class AddKStringConversion extends CopyOnWriteTransformer {

    private static final KLabelConstant KLabel2String =
            KLabelConstant.of("KLabel2String");

    private static final String String2KLabelCons =
            "KLabel1String2KLabelSyn";

    public AddKStringConversion(Context context) {
        super("Define KLabel2String and String2Klabel for KLabel constants", context);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        /* TODO: escape labels when generating KLabel2String and String2KLabel */
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (String klbl : node.getModuleKLabels()) {
            Term kapp = KApp.of(new KInjectedLabel(KLabelConstant.of(klbl, context)));
            Term lhs = KApp.of(KLabel2String, kapp);
            Term rhs = StringBuiltin.kAppOf(StringUtil.escapeMaude(klbl));
            Rule rule = new Rule(lhs, rhs, context);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);

            java.util.List<Term> termList = new ArrayList<Term>();
            termList.add(rhs);
            TermCons termCons = new TermCons(KSorts.KLABEL, String2KLabelCons, termList, context);
            rule = new Rule(termCons, KLabelConstant.of(klbl, context), context);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

}

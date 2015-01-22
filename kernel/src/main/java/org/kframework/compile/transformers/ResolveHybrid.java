// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;
import java.util.List;

public class ResolveHybrid extends CopyOnWriteTransformer {

    private List<ModuleItem> hybrids = new ArrayList<ModuleItem>();

    public ResolveHybrid(Context context) {
        super("Resolve Hybrid", context);
    }


    @Override
    public ASTNode visit(Module node, Void _void)  {
        hybrids.clear();
        super.visit(node, _void);
        if (hybrids.isEmpty()) return node;
        node = node.shallowCopy();
        hybrids.addAll(node.getItems());
        node.setItems(hybrids);
        return node;
    }

    @Override
    public ASTNode visit(Production node, Void _void)  {
        if (!node.containsAttribute("hybrid") && !node.isListDecl()) return node;
        Rule rule = new Rule();
        rule.setBody(new Rewrite(
                KApp.of(KLabelConstant.KRESULT_PREDICATE,
                        KApp.of(KLabelConstant.of(node.getKLabel()),
                                 new Variable("K", Sort.K), new Variable("Ks", Sort.KLIST))),
                KApp.of(KLabelConstant.KRESULT_PREDICATE, new Variable("Ks", Sort.KLIST)), context));
        rule.setRequires(new KApp(
                KLabelConstant.KRESULT_PREDICATE,
                new Variable("K", Sort.K)));

        rule.addAttribute(Attribute.FUNCTION);
        hybrids.add(rule);
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

        return node;
    }


}

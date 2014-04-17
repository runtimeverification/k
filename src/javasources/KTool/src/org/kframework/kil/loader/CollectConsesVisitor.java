// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectConsesVisitor extends BasicVisitor {
    public CollectConsesVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Production node, Void _) {
        if (node.containsAttribute(Constants.CONS_cons_ATTR)) {
            String cons = node.getAttribute(Constants.CONS_cons_ATTR);
            context.conses.put(cons, node);
            context.putLabel(node, cons);
        }
        if (node.isListDecl()) {
            context.listConses.put(node.getSort(), node);
            context.putListLabel(node);
        }
        for (Attribute a : node.getAttributes().getContents()) {
            String key = a.getKey();
            if (key.equals("klabel"))
                key = node.getAttribute("klabel");
            if (context.productions.containsKey(key)) {
                context.productions.get(key).add(node);
            } else {
                Set<Production> sset = new HashSet<Production>();
                sset.add(node);
                context.productions.put(key, sset);
            }
        }
        return null;
    }
}

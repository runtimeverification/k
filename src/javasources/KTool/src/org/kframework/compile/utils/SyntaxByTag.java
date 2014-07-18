// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;


public class SyntaxByTag extends BasicVisitor {
    private final Set<Production> productions = new HashSet<Production>();
    private final String key;
    private final boolean prefix;

    @Override
    public Void visit(Configuration node, Void _) { return null; }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _) { return null; }

    @Override
    public Void visit(Rule node, Void _) { return null; }

    @Override
    public Void visit(Production node, Void _) {
        if (key.equals("") || node.containsAttribute(key, prefix))
            productions.add(node);
        return null;
    };

    public SyntaxByTag(String key, Context context) {
        this(key, false, context);
    }

    public SyntaxByTag(String key, boolean prefix, Context context) {
        super(context);
        this.key = key;
        this.prefix = prefix;
    }

    public Set<Production> getProductions() {
        return productions;
    }

    public static Set<Production> get(ASTNode node, String key, Context context) {
        return get(node, key, false, context);
    }

    public static Set<Production> get(ASTNode node, String key, boolean prefix, Context context) {
        SyntaxByTag visitor = new SyntaxByTag(key, prefix, context);
        visitor.visitNode(node);
        return visitor.getProductions();
    }

}

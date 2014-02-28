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
    public void visit(Configuration node) { return; }
    
    @Override
    public void visit(org.kframework.kil.Context node) { return; }
    
    @Override
    public void visit(Rule node) { return; }
    
    @Override
    public void visit(Production node) {
        if (key.equals("") || node.containsAttribute(key, prefix))
            productions.add(node);
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
        node.accept(visitor);
        return visitor.getProductions();
    }
    
}

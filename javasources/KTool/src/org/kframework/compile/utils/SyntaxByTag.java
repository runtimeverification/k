package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;


public class SyntaxByTag extends BasicVisitor {
	private final Set<Production> productions = new HashSet<Production>();
	private final String key;
	
	@Override
	public void visit(Configuration node) { return; }
	
	@Override
	public void visit(Context node) { return; }
	
	@Override
	public void visit(Rule node) { return; }
	
	@Override
	public void visit(Production node) {
		if (key.equals("") || node.containsAttribute(key))
			productions.add(node);
	};

    public SyntaxByTag(String key, DefinitionHelper definitionHelper) {
    	super(definitionHelper);
        this.key = key;
    }

    public Set<Production> getProductions() {
        return productions;
    }

	public static Set<Production> get(ASTNode node, String key, DefinitionHelper definitionHelper) {
		SyntaxByTag visitor = new SyntaxByTag(key, definitionHelper);
		node.accept(visitor);
		return visitor.getProductions();
	}
	
}

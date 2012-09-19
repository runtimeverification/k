package org.kframework.compile.utils;

import java.util.ArrayList;
import java.util.List;

import org.kframework.k.ASTNode;
import org.kframework.k.Configuration;
import org.kframework.k.Production;
import org.kframework.visitors.BasicVisitor;


public class GetSyntaxByTag extends BasicVisitor {
	List<Production> productions = new ArrayList<Production>();
	private String key;
	
	@Override
	public void visit(Configuration node) {return;}
	
	@Override
	public void visit(org.kframework.k.Context node) {return;};
	
	@Override
	public void visit(org.kframework.k.Rule node) {return;};
	
	@Override
	public void visit(Production node) {
		if (node.getAttributes().containsKey(key))
			productions.add(node);
	};
	
	public static List<Production> applyVisitor(ASTNode node, 
			String key) {
		GetSyntaxByTag visitor = new GetSyntaxByTag();
		visitor.key = key;
		node.accept(visitor);
		return visitor.productions;
	}
	
}

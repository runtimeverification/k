package org.kframework.compile.utils;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;


public class GetSyntaxByTag extends BasicVisitor {
	List<Production> productions = new ArrayList<Production>();
	private String key;
	
	@Override
	public void visit(Configuration node) {return;}
	
	@Override
	public void visit(org.kframework.kil.Context node) {return;};
	
	@Override
	public void visit(org.kframework.kil.Rule node) {return;};
	
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

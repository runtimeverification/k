package ro.uaic.info.fmse.compile.utils;

import java.util.ArrayList;
import java.util.List;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class GetSyntaxByTag extends BasicVisitor {
	List<Production> productions = new ArrayList<Production>();
	private String key;
	
	@Override
	public void visit(Configuration node) {return;}
	
	@Override
	public void visit(ro.uaic.info.fmse.k.Context node) {return;};
	
	@Override
	public void visit(ro.uaic.info.fmse.k.Rule node) {return;};
	
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

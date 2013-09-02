package org.kframework.kcheck;

import java.util.LinkedList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class RetrieveRRVisitor extends BasicVisitor {

	List<ASTNode> rules = new LinkedList<ASTNode>();
	
	public RetrieveRRVisitor(Context context) {
		super(context);
	}

	@Override
	public void visit(Rule node) {
		rules.add(node);
		super.visit(node);
	}
	
	public List<ASTNode> getRules() {
		return rules;
	}
}

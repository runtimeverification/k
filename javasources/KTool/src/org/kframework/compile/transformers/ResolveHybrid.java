package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ResolveHybrid extends CopyOnWriteTransformer {

	private List<ModuleItem> hybrids = new ArrayList<ModuleItem>();

	public ResolveHybrid() {
		super("Resolve Hybrid");
	}
	
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		hybrids.clear();
		super.transform(node);
		if (hybrids.isEmpty()) return node;
		node = node.shallowCopy();
		hybrids.addAll(node.getItems());
		node.setItems(hybrids);
		return node;
	}
	
	@Override
	public ASTNode transform(Production node) throws TransformerException {
		if (!node.getAttributes().containsKey("hybrid")) return node;
		Rule rule = new Rule();
		rule.setBody(new Rewrite(
				new KApp(new Constant("KLabel", "isKResult"), 
						new KApp(new Constant("KLabel", node.getKLabel()), new Variable("Ks", "List{K}"))), 
						new KApp(new KInjectedLabel(new Constant("#Bool", "true")),new Empty("List{K}"))));
		rule.setCondition(new KApp(new Constant("KLabel", "isKResult"), new Variable("Ks", "List{K}")));
		rule.getAttributes().getContents().add(new Attribute("predicate", ""));
		hybrids.add(rule);
		return node;
	}
	
	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		
		return node;
	}
	
	@Override
	public ASTNode transform(Context node) throws TransformerException {
		
		return node;
	}
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		
		return node;
	}
	
 
}

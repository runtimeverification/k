package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.GetSyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Attribute;
import org.kframework.k.Constant;
import org.kframework.k.KApp;
import org.kframework.k.Module;
import org.kframework.k.ModuleItem;
import org.kframework.k.Production;
import org.kframework.k.Rewrite;
import org.kframework.k.Rule;
import org.kframework.visitors.CopyOnWriteTransformer;


public class ResolveBinder extends CopyOnWriteTransformer {

	public ResolveBinder() {
		super("Resolve binder");
	}
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		List<Production> prods = GetSyntaxByTag.applyVisitor(node, "binder");
		if (prods.isEmpty()) return node;
		List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
		node = node.shallowCopy();
		for (Production prod : prods) {
			Rule rule = new Rule();
			rule.setBody(
					new Rewrite(
							new KApp(new Constant("KLabel", "isBinder"), 
									MetaK.getTerm(prod)), 
							new Constant("#Bool", "true"))
					);
			rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
			items.add(rule);
		}
		node.setItems(items);
		return node;
	}
}

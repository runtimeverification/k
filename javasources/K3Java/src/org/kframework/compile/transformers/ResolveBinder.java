package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.GetSyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


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

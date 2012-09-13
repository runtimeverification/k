package ro.uaic.info.fmse.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import ro.uaic.info.fmse.compile.utils.GetSyntaxByTag;
import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Attribute;
import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.KApp;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.ModuleItem;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.Rewrite;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

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

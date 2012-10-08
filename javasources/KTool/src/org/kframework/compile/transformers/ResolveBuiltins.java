package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.KApp;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ResolveBuiltins extends CopyOnWriteTransformer {
	
	Set<String> builtinSorts = new HashSet<String>();

	public ResolveBuiltins() {
		super("Resolve Builtins");
	}
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		builtinSorts.clear();
		super.transform(node);
		if (builtinSorts.isEmpty()) return node;
		node = node.shallowCopy();
		List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
		List<PriorityBlock> priorities = new ArrayList<PriorityBlock>();
		PriorityBlock block = new PriorityBlock();
		priorities.add(block );
		Syntax syn = new Syntax(new Sort("KLabel"), priorities);
		items.add(syn);
		for (String sort : builtinSorts) {
			List<ProductionItem> pItems = new ArrayList<ProductionItem>();
			Production p = new Production(new Sort("KLabel"), pItems );
			pItems.add(new Terminal("#"));
			pItems.add(new Sort(sort));
			p.getAttributes().set("KLabelWrapper", sort);
			p.getAttributes().set("cons", "KLabel1" + sort + "Wrapper");
			p.getAttributes().set("prefixlabel", "#_");			
			DefinitionHelper.conses.put("KLabel1" + sort + "Wrapper", p);
			block.getProductions().add(p);
			pItems = new ArrayList<ProductionItem>();
			p = new Production(new Sort("KLabel"), pItems );
			pItems.add(new Terminal("is" + sort));
			block.getProductions().add(p);
			Rule rule = new Rule();
			rule.setBody(new Rewrite(
					new KApp(new Constant("KLabel", "is" + sort), 
							new Variable(sort, sort)), 
					new Constant("#Bool", "true")));
			rule.getAttributes().getContents().add(new Attribute("predicate", ""));
			items.add(rule);
			
		}
		node.setItems(items);
		return node;
	}
	
	@Override
	public ASTNode transform(Sort node) throws TransformerException {
		if (MetaK.isBuiltinSort(node.getName()))
				builtinSorts.add(node.getName());
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

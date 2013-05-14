package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ResolveBuiltins extends CopyOnWriteTransformer {
	
	Set<String> builtinSorts = new HashSet<String>();

	public ResolveBuiltins(DefinitionHelper definitionHelper) {
		super("Resolve Builtins", definitionHelper);
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
		Syntax syn = new Syntax(new Sort(KSorts.KLABEL), priorities);
		items.add(syn);
		for (String sort : builtinSorts) {
			List<ProductionItem> pItems = new ArrayList<ProductionItem>();
			Production p = new Production(new Sort(KSorts.KLABEL), pItems );
			pItems.add(new Terminal("#"));
			pItems.add(new Sort(sort));
			p.putAttribute("KLabelWrapper", sort);
			p.putAttribute("cons", "KLabel1" + sort + "Wrapper");
			p.putAttribute("prefixlabel", "#_");
			definitionHelper.conses.put("KLabel1" + sort + "Wrapper", p);
			definitionHelper.putLabel(p, "KLabel1" + sort+ "Wrapper");
			block.getProductions().add(p);
			pItems = new ArrayList<ProductionItem>();
			p = new Production(new Sort(KSorts.KLABEL), pItems );
			pItems.add(new Terminal("is" + sort));
			block.getProductions().add(p);
			Rule rule = new Rule();
			rule.setBody(new Rewrite(
					KApp.of(definitionHelper, KLabelConstant.of(AddPredicates.predicate(sort), definitionHelper),
							new Variable(sort, sort)),
                    BoolBuiltin.TRUE, definitionHelper));
			rule.addAttribute(Attribute.PREDICATE);
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

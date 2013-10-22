package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Class adding #_ : Builtin -> KLabel wrappers and is#Builtin predicates for each builtin.
 *
 * andreis: this is backend specific, should go to MaudeFilter or something...
 */
public class ResolveBuiltins extends CopyOnWriteTransformer {
	
	Set<String> builtinSorts = new HashSet<String>();

	public ResolveBuiltins(Context context) {
		super("Resolve Builtins", context);
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
			context.conses.put("KLabel1" + sort + "Wrapper", p);
			context.putLabel(p, "KLabel1" + sort+ "Wrapper");
			block.getProductions().add(p);
			pItems = new ArrayList<ProductionItem>();
			p = new Production(new Sort(KSorts.KLABEL), pItems );
			pItems.add(new Terminal("is" + sort));
			block.getProductions().add(p);
			Rule rule = new Rule();
			rule.setBody(new Rewrite(
					KApp.of(KLabelConstant.of(AddPredicates.predicate(sort), context),
							new Variable(sort, sort)),
                    BoolBuiltin.TRUE, context));
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
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		return node;
	}

}

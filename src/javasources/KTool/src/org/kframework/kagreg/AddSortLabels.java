package org.kframework.kagreg;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.AddConsesVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddSortLabels extends CopyOnWriteTransformer {
	
	final protected List<String> labeledSorts;

	public AddSortLabels(Context context, List<String> labeledSorts) {
		super("AddSortLabels", context);
		this.labeledSorts = labeledSorts;
	}
	
	@Override
	public ASTNode transform(Module module) throws TransformerException {
		if (module.isPredefined()) {
			return module;
		}
		return super.transform(module);
	}
	
	@Override
	public ASTNode transform(Syntax syntax) throws TransformerException {
		if (labeledSorts.contains(syntax.getSort().getName())) {
			return syntax;
		}
		labeledSorts.add(syntax.getSort().getName());
		List<ProductionItem> productionItems = new ArrayList<ProductionItem>();
		productionItems.add(new Terminal("L" + syntax.getSort()));
		productionItems.add(new Sort("Id"));
		productionItems.add(new Terminal(":"));
		productionItems.add(syntax.getSort());
		Production production = new Production(syntax.getSort(), productionItems);

//		System.out.println("Before: " + context.conses);
		AddConsesVisitor acv = new AddConsesVisitor(context);
		production.accept(acv);
//		System.out.println("After: " + context.conses);
//		acv.visit(production);
		List<PriorityBlock> priorityBlocks = syntax.getPriorityBlocks();
		if (priorityBlocks.size() == 0) {
			System.out.println(syntax.getSort() + " empty priorityBlocks");
			PriorityBlock priorityBlock = new PriorityBlock();
			List<Production> productions = new ArrayList<Production>();
			productions.add(production);
			priorityBlock.setProductions(productions);
			priorityBlocks.add(priorityBlock);
		} else {
			priorityBlocks.get(priorityBlocks.size() - 1).getProductions().add(production);
		}
		syntax.setPriorityBlocks(priorityBlocks);
		return syntax;
	}
}

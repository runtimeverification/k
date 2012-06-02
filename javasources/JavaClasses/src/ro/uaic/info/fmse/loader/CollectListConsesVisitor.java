package ro.uaic.info.fmse.loader;

import java.util.List;

import ro.uaic.info.fmse.k.PriorityBlock;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.ProductionItem;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class CollectListConsesVisitor extends BasicVisitor {

	@Override
	public void visit(Syntax syntax) {
		List<PriorityBlock> pb = syntax.getPriorityBlocks();
		for (PriorityBlock p : pb) {
			List<Production> nodes = p.getProductions();
			for (Production node : nodes) {
				List<ProductionItem> items = node.getItems();
				for (ProductionItem it : items)
					if (it instanceof UserList)
						DefinitionHelper.listConses.put(syntax.getSort()
								.toString(), node);
			}
		}
	}
}

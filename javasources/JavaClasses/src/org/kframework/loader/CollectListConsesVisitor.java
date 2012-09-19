package org.kframework.loader;

import org.kframework.k.Production;
import org.kframework.k.ProductionItem.ProductionType;
import org.kframework.visitors.BasicVisitor;

public class CollectListConsesVisitor extends BasicVisitor {

	@Override
	public void visit(Production prd) {
		if (prd.getItems().size() == 1 && prd.getItems().get(0).getType() == ProductionType.USERLIST)
			DefinitionHelper.listConses.put(prd.getSort(), prd);
	}
}

package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectListConsesVisitor extends BasicVisitor {

	@Override
	public void visit(Production prd) {
		if (prd.getItems().size() == 1 && prd.getItems().get(0).getType() == ProductionType.USERLIST)
			DefinitionHelper.listConses.put(prd.getSort(), prd);
	}
}

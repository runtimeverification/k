package org.kframework.loader;

import org.kframework.k.Production;
import org.kframework.k.ProductionItem;
import org.kframework.k.Sort;
import org.kframework.k.UserList;
import org.kframework.k.ProductionItem.ProductionType;
import org.kframework.visitors.BasicVisitor;

public class CollectSubsortsVisitor extends BasicVisitor {

	public void visit(Production prd) {
		if (!Sort.isBasesort(prd.getSort()))
			DefinitionHelper.addSubsort("K", prd.getSort());
		if (prd.isSubsort()) {
			Sort srt = (Sort) prd.getItems().get(0);
			DefinitionHelper.addSubsort(prd.getSort(), srt.toString());
		} else if (prd.isListDecl()) {
			UserList srt = (UserList) prd.getItems().get(0);
			DefinitionHelper.addSubsort(prd.getSort(), srt.getSort());
			DefinitionHelper.listConses.put(prd.getSort(), prd);
		} else {
			for (ProductionItem pi : prd.getItems()) {
				if (pi.getType() == ProductionType.SORT) {
					Sort s = (Sort) pi;
					if (!s.isBaseSort())
						DefinitionHelper.addSubsort("K", s.getName());
				}
			}
		}
	}
}

package ro.uaic.info.fmse.loader;

import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.ProductionItem;
import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.visitors.BasicVisitor;

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

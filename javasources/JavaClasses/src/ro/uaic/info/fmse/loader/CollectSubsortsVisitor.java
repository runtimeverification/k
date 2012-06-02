package ro.uaic.info.fmse.loader;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class CollectSubsortsVisitor extends BasicVisitor {
	public void visit(Syntax syn) {
		for (PriorityBlock pb : syn.getPriorityBlocks()) {
			for (Production prd : pb.getProductions()) {
				if (prd.getItems().size() == 1 && prd.getItems().get(0).getType() == ProductionType.SORT) {
					Sort srt = (Sort) prd.getItems().get(0);
					DefinitionHelper.addSubsort(syn.getSort().toString(), srt.toString());
				}
				if (prd.getItems().size() == 1 && prd.getItems().get(0).getType() == ProductionType.USERLIST) {
					UserList srt = (UserList) prd.getItems().get(0);
					DefinitionHelper.addSubsort(syn.getSort().toString(), srt.getSort().toString());
					DefinitionHelper.listConses.put(syn.getSort().toString(), prd);
				}
			}
		}
		super.visit(syn);
	}
}

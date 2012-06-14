package ro.uaic.info.fmse.loader;

import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class CollectSubsortsVisitor extends BasicVisitor {

	public void visit(Production prd) {
		if (prd.isSubsort()) {
			Sort srt = (Sort) prd.getItems().get(0);
			DefinitionHelper.addSubsort(prd.getSort(), srt.toString());
		}
		if (prd.isListDecl()) {
			UserList srt = (UserList) prd.getItems().get(0);
			DefinitionHelper.addSubsort(prd.getSort(), srt.getSort());
			DefinitionHelper.listConses.put(prd.getSort(), prd);
		}
	}

	// TODO: eliminate the code below
	// although, make sure you call CollectConsesVisitor first to add the sort to productions

	// public void visit(Syntax syn) {
	// for (PriorityBlock pb : syn.getPriorityBlocks()) {
	// for (Production prd : pb.getProductions()) {
	// if (prd.getItems().size() == 1 && prd.getItems().get(0).getType() == ProductionType.SORT) {
	// Sort srt = (Sort) prd.getItems().get(0);
	// DefinitionHelper.addSubsort(syn.getSort().toString(), srt.toString());
	// }
	// if (prd.getItems().size() == 1 && prd.getItems().get(0).getType() == ProductionType.USERLIST) {
	// UserList srt = (UserList) prd.getItems().get(0);
	// DefinitionHelper.addSubsort(syn.getSort().toString(), srt.getSort().toString());
	// DefinitionHelper.listConses.put(syn.getSort().toString(), prd);
	// }
	// }
	// }
	// super.visit(syn);
	// }
}

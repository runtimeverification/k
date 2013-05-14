package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.UserList;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectSubsortsVisitor extends BasicVisitor {

	public CollectSubsortsVisitor(DefinitionHelper definitionHelper) {
		super(definitionHelper);
		// TODO Auto-generated constructor stub
	}

	public void visit(Definition def) {
		super.visit(def);
		definitionHelper.finalizeSubsorts();
	}

	public void visit(Production prd) {
		if (!Sort.isBasesort(prd.getSort()))
			definitionHelper.addSubsort("K", prd.getSort());
		if (prd.isSubsort()) {
			Sort srt = (Sort) prd.getItems().get(0);
			definitionHelper.addSubsort(prd.getSort(), srt.toString());
		} else if (prd.isListDecl()) {
			UserList srt = (UserList) prd.getItems().get(0);
			definitionHelper.listConses.put(prd.getSort(), prd);
			definitionHelper.putListLabel(prd);
			definitionHelper.addSubsort(prd.getSort(), srt.getSort());
		} else {
			for (ProductionItem pi : prd.getItems()) {
				if (pi.getType() == ProductionType.SORT) {
					Sort s = (Sort) pi;
					if (!s.isBaseSort())
						definitionHelper.addSubsort("K", s.getName());
				}
			}
		}
	}
}

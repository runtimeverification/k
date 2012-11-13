package org.kframework.kil.loader;

import org.kframework.kil.Constant;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityBlockExtended;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectPrioritiesVisitor extends BasicVisitor {

	public void visit(Syntax node) {
		for (int i = 0; i < node.getPriorityBlocks().size() - 1; i++) {
			PriorityBlock pb1 = node.getPriorityBlocks().get(i);
			PriorityBlock pb2 = node.getPriorityBlocks().get(i + 1);
			for (Production prd1 : pb1.getProductions()) {
				// allow priorities only between productions that have a sort at the left or right
				if (prd1.isSubsort() || prd1.isConstant())
					continue;
				if (prd1.getItems().get(0).getType() != ProductionType.SORT && prd1.getItems().get(prd1.getItems().size() - 1).getType() != ProductionType.SORT)
					continue;
				for (Production prd2 : pb2.getProductions()) {
					if (prd2.isSubsort() || prd2.isConstant())
						continue;
					if (prd2.getItems().get(0).getType() != ProductionType.SORT && prd2.getItems().get(prd2.getItems().size() - 1).getType() != ProductionType.SORT)
						continue;
					DefinitionHelper.addPriority(prd1.getKLabel(), prd2.getKLabel());
				}
			}
		}
	}

	public void visit(PriorityExtended node) {
		for (int i = 0; i < node.getPriorityBlocks().size() - 1; i++) {
			PriorityBlockExtended pb1 = node.getPriorityBlocks().get(i);
			PriorityBlockExtended pb2 = node.getPriorityBlocks().get(i + 1);
			for (Constant prd1 : pb1.getProductions()) {
				for (Constant prd2 : pb2.getProductions()) {
					DefinitionHelper.addPriority(prd1.getValue(), prd2.getValue());
				}
			}
		}
	}
}

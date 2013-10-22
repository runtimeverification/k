package org.kframework.kil.loader;

import java.util.Set;

import org.kframework.kil.Definition;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityBlockExtended;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.SDFHelper;

public class CollectPrioritiesVisitor extends BasicVisitor {

	public CollectPrioritiesVisitor(Context context) {
		super(context);
	}

	public void visit(Definition def) {
		super.visit(def);
		context.finalizePriority();
	}

	public void visit(Syntax node) {
		for (int i = 0; i < node.getPriorityBlocks().size() - 1; i++) {
			PriorityBlock pb1 = node.getPriorityBlocks().get(i);
			PriorityBlock pb2 = node.getPriorityBlocks().get(i + 1);
			for (Production prd1 : pb1.getProductions()) {
				// allow priorities only between productions that have a sort at the left or right
				if (prd1.isSubsort() || prd1.isConstant())
					continue;
				if (!(prd1.getItems().get(0) instanceof Sort) && !(prd1.getItems().get(prd1.getItems().size() - 1) instanceof Sort))
					continue;
				for (Production prd2 : pb2.getProductions()) {
					if (prd2.isSubsort() || prd2.isConstant())
						continue;
					if (!(prd2.getItems().get(0) instanceof Sort) && !(prd2.getItems().get(prd2.getItems().size() - 1) instanceof Sort))
						continue;
					context.addPriority(prd1.getKLabel(), prd2.getKLabel());
				}
			}
		}
	}

	public void visit(PriorityExtended node) {
		for (int i = 0; i < node.getPriorityBlocks().size() - 1; i++) {
			PriorityBlockExtended pb1 = node.getPriorityBlocks().get(i);
			PriorityBlockExtended pb2 = node.getPriorityBlocks().get(i + 1);
			// example: syntax priorities tag1 > tag2
			for (KLabelConstant prd1 : pb1.getProductions()) {
				// get all the productions annotated with tag1
				Set<Production> prods1 = SDFHelper.getProductionsForTag(prd1.getLabel(), context);
				for (KLabelConstant prd2 : pb2.getProductions()) {
					// get all the productions annotated with tag2
					Set<Production> prods2 = SDFHelper.getProductionsForTag(prd2.getLabel(),
                            context);
					// add all the relations between all the productions annotated with tag1 and tag 2
					for (Production p1 : prods1) {
						if (p1.isSubsort() && !p1.containsAttribute("klabel"))
							continue;
						for (Production p2 : prods2) {
							if (p2.isSubsort() && !p2.containsAttribute("klabel"))
								continue;
							context.addPriority(p1.getKLabel(), p2.getKLabel());
						}
					}
				}
			}
		}
	}
}

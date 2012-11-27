package org.kframework.kil.loader;

import java.util.Set;

import org.kframework.kil.Constant;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.SDFHelper;

public class UpdateAssocVisitor extends BasicVisitor {
	/**
	 * Because the block associativity is not reflexive in SDF, I have to add it manually.
	 */
	@Override
	public void visit(PriorityExtendedAssoc pri) {
		for (Constant c : pri.getTags()) {
			Set<Production> prods = SDFHelper.getProductionsForTag(c.getValue());
			for (Production p : prods) {
				if (!p.getAttributes().containsKey("left") && !p.getAttributes().containsKey("right") && !p.getAttributes().containsKey("non-assoc")) {
					p.getAttributes().addAttribute(pri.getAssoc(), "");
					System.out.println("Adding: " + pri.getAssoc());
				}
			}
		}
	}
}

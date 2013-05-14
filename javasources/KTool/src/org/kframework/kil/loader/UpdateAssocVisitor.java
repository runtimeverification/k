package org.kframework.kil.loader;

import java.util.Set;

import org.kframework.kil.Constant;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.SDFHelper;

public class UpdateAssocVisitor extends BasicVisitor {
	public UpdateAssocVisitor(DefinitionHelper definitionHelper) {
		super(definitionHelper);
	}

	/**
	 * Because the block associativity is not reflexive in SDF, I have to add it manually.
	 */
	@Override
	public void visit(PriorityExtendedAssoc pri) {
		for (KLabelConstant c : pri.getTags()) {
			Set<Production> prods = SDFHelper.getProductionsForTag(c.getLabel(), definitionHelper);
			for (Production p : prods) {
				definitionHelper.putAssoc(p.getCons(), prods);
				if (!p.getAttributes().containsKey("left") && !p.getAttributes().containsKey("right") && !p.getAttributes().containsKey("non-assoc")) {
					p.addAttribute(pri.getAssoc(), "");
				}
			}
		}
	}

	@Override
	public void visit(PriorityBlock pri) {
		if (!pri.getAssoc().equals("")) {
			for (Production p : pri.getProductions()) {
				definitionHelper.putAssoc(p.getCons(), pri.getProductions());
			}
		}
	}
}

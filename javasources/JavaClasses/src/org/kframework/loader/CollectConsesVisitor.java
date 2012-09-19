package org.kframework.loader;

import org.kframework.k.Production;
import org.kframework.visitors.BasicVisitor;

public class CollectConsesVisitor extends BasicVisitor {
	@Override
	public void visit(Production node) {
		if (node.getAttributes().containsKey(Constants.CONS_cons_ATTR))
			DefinitionHelper.conses.put(node.getAttributes().get(Constants.CONS_cons_ATTR), node);
	}
}

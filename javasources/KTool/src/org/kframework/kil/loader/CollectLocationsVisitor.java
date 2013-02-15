package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.Sentence;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectLocationsVisitor extends BasicVisitor {
	@Override
	public void visit(Production node) {
		DefinitionHelper.locations.put(node.getFilename() + ":" + node.getLocation(), node);
	}

	@Override
	public void visit(Sentence node) {
		DefinitionHelper.locations.put(node.getFilename() + ":" + node.getLocation(), node);
	}
}

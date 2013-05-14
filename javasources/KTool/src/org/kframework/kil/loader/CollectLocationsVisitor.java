package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.Sentence;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectLocationsVisitor extends BasicVisitor {
	public CollectLocationsVisitor(DefinitionHelper definitionHelper) {
		super(definitionHelper);
		// TODO Auto-generated constructor stub
	}

	@Override
	public void visit(Production node) {
		definitionHelper.locations.put(node.getFilename() + ":" + node.getLocation(), node);
	}

	@Override
	public void visit(Sentence node) {
		definitionHelper.locations.put(node.getFilename() + ":" + node.getLocation(), node);
	}
}

package org.kframework.kil.loader;

import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Sentence;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectConfigCellsVisitor extends BasicVisitor {
	@Override
	public void visit(Configuration config) {
		super.visit((Sentence) config);
	}

	@Override
	public void visit(Sentence s) {
	}

	@Override
	public void visit(Cell cell) {
		DefinitionHelper.addCellDecl(cell);
		super.visit(cell);
	}
}

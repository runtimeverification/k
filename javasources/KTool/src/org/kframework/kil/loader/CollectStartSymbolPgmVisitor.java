package org.kframework.kil.loader;

import org.kframework.kil.Context;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectStartSymbolPgmVisitor extends BasicVisitor {

	@Override
	public void visit(Rule node) {
	}

	@Override
	public void visit(Context node) {
	}

	@Override
	public void visit(Syntax node) {
	}

	@Override
	public void visit(Variable node) {
		if (node.getName().equals("$PGM")) {
			String sort = node.getSort();
			if (DefinitionHelper.isSubsorted(DefinitionHelper.startSymbolPgm, sort))
				DefinitionHelper.startSymbolPgm = sort;
		}
	}
}

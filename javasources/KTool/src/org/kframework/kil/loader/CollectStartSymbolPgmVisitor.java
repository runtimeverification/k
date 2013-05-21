package org.kframework.kil.loader;

import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;

/**
 * Collect the $PGM sort from the final configuration it encounters
 * 
 * @author Radu
 * 
 */
public class CollectStartSymbolPgmVisitor extends BasicVisitor {

	public CollectStartSymbolPgmVisitor(Context context) {
		super(context);
	}

	@Override
	public void visit(Rule node) {
	}

	@Override
	public void visit(org.kframework.kil.Context node) {
	}

	@Override
	public void visit(Syntax node) {
	}

	@Override
	public void visit(Variable node) {
		if (node.getName().equals("$PGM")) {
			context.startSymbolPgm = node.getSort();
		}
	}
}

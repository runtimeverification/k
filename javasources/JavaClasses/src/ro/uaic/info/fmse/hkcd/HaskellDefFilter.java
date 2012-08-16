package ro.uaic.info.fmse.hkcd;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicVisitor;

/**
 * Transform AST of language definition into set of Haskell
 * constructors.
 *
 * @see ProgramLoader.loadPgmAst
 */
public class HaskellDefFilter extends HaskellFilter {
	/**
	 * When true, the filter is processing LHS of a rewrite.
	 */
	private boolean lhs = false;

	/**
	 * For rules we need to produce a pattern to match the
	 * constructor for the LHS, and use names of patterns in RHS.
	 */
	public void visit(Rewrite r) {
		lhs = true;
		r.getLeft().accept(this);
		result += " => ";
		lhs = false;
		r.getRight().accept(this);
		result += endl;
	}

	/**
	 * When on LHS, produce a pattern to match constructor for
	 * sort of variable. Name of variable will be used as name of
	 * pattern.
	 */
	public void visit(Variable var) {
		if (lhs) {
			String l = var.getLocation();
			String f = var.getFilename();
			Constant cst = new Constant(l, f);
			
			cst.setSort("#" + var.getSort());
			cst.setValue("_");
			
			result += var.getName() + "@(";
			cst.accept(this);
			result += ")";
		} else {
			result += var.getName();
		}
	}
}

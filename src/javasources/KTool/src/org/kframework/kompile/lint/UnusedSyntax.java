package org.kframework.kompile.lint;

import org.kframework.kil.*;

import java.util.ArrayList;

/**
 *  This class is a lint rule that checks for unused syntaxes on the productions
 */
public class UnusedSyntax extends KlintRule {

	@SuppressWarnings("unused")
	private static boolean debug = false;

	public UnusedSyntax(Definition javaDef, org.kframework.kil.loader.Context context) {
		super(context);
		this.javaDef = javaDef;
	}

	@Override
	public void run() {
		ArrayList<Production> productions = getProductions();
		ArrayList<Rewrite> rewrites = getRewrites(true);

		for (Production production : productions) {
			if(!hasRewrite(production, rewrites))
				warning("Unused syntax: ", (ASTNode)production);
		}
	}

	/**
	 * Checks if a given production has a rewrite on a list of rewrites
	 * @param production the production to be checked
	 * @param rewrites a list of rewrites
	 * @return true if the production is on the rewrite list, false otherwise
	 */
	private boolean hasRewrite(Production production, ArrayList<Rewrite> rewrites) {
		for(Rewrite rewrite : rewrites){
			Term term = rewrite.getLeft();

			/* If is a cell, goes deep in it looking for a termCons */
			if(term instanceof Cell){
				Cell cell = (Cell)term;
				while(cell.getContents() instanceof Cell){
					cell = (Cell)cell.getContents();
				}
				term = cell.getContents();
			}

			/* If is a termcons, check it agains the productions */
			if(term instanceof TermCons){
				TermCons termCons = (TermCons)term;
				Production termProd = context.conses.get("\""+termCons.getCons()+"\"");
				if(termProd.equals(production))
					return true;
			}
		}
		return false;
	}
}

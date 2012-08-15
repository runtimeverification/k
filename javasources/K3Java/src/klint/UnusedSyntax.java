package klint;

import java.util.ArrayList;
import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;

public class UnusedSyntax extends KlintRule {

	private static boolean debug = false;

	public UnusedSyntax(Definition javaDef) {
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
				Production termProd = DefinitionHelper.conses.get("\""+termCons.getCons()+"\"");
				if(termProd.equals(production))
					return true;
			}
		}
		return false;
	}
}

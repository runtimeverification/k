/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package klint;

import java.util.ArrayList;
import ro.uaic.info.fmse.k.*;

/**
 * @author fotanus
 *
 * This classes looks for names declared on the left side of a rule that aren't
 * used on the right side.
 */
public class UnusedName extends KlintRule{

	public UnusedName(Definition javaDef){
		this.javaDef = javaDef;
	}

	@Override
	public void run() {

		/* Handles rules simple rewrites; the ones that aren't in a bag */
		for(Rewrite rewrite : getRewrites(false)){
			ArrayList<Variable> leftVars = getVariables(rewrite.getLeft());
			ArrayList<Variable> rightVars = getVariables(rewrite.getRight());
			containsAllVariables(rewrite, leftVars, rightVars);
		}

		/* Handle rules that are a collection; basically acumulates the left
		 variables while checking the contents from collections individually, and
		 then evaluate if all left vars are really used.*/
		for(Collection collection : getRuleCollections()){
			for(Term term : collection.getContents()){
				ArrayList<Variable> allLeftVars = new ArrayList<Variable>();
				ArrayList<Variable> allRightVars = new ArrayList<Variable>();
				if(term instanceof Rewrite){
					Rewrite rewrite = (Rewrite)term;
					allLeftVars.addAll(getVariables(rewrite.getLeft()));
					ArrayList<Variable> rightVars = getVariables(rewrite.getRight());
					allRightVars.addAll(rightVars);
					containsAllVariables(rewrite, allLeftVars, rightVars);
				}
				containsAllVariables(collection, allRightVars, allLeftVars);
			}
		}


	}


	/**
	 * This function checkes in a giving rewrite rule for unused variables. If this
	 * rewrite has other recursive rewrites, it checks on these as well.
	 *
	 * @param rewrite the rewrite rule that will be checked
	 */
	private void containsAllVariables(Term rule, ArrayList<Variable> leftVars, ArrayList<Variable> rightVars){

		rightVars = deleteAnonymous(rightVars);
		leftVars = deleteAnonymous(leftVars);

		if(!rightVars.containsAll(leftVars)){
			warning("Unused left variable on rule: ", (ASTNode) rule);
		}
		if(!leftVars.containsAll(rightVars)){
			warning("Using undefined variable on te right of a rule :", (ASTNode) rule);
		}
	}

	/**
	 * Giving a term, get all variables that are under it on the AST.
	 *
	 * @param term the term to be checked.
	 * @return a list of all variables from the term
	 */
	private static ArrayList<Variable> getVariables(Term term){
		ArrayList<Variable> ret = new ArrayList<Variable>();
		if(term instanceof Variable){
			ret.add((Variable)term);
		}else if(term instanceof Collection){
			Collection collection = (Collection)term;
			for(Term t : collection.getContents()){
				ret.addAll(getVariables(t));
			}
		}else if(term instanceof TermCons){
			TermCons termCons = (TermCons)term;
			for(Term t : termCons.getContents()){
				ret.addAll(getVariables(t));
			}
		}
		return ret;
	}

}

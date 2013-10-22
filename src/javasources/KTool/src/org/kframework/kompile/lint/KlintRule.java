package org.kframework.kompile.lint;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;

/**
 * A Klint rule is an algorithm that giving the AST of a K file will detect a
 * type of mistake.
 *
 * To Create a new rule, extend this class and create the algorithm to this rule.
 * Afterwards, import this class on KompileFrontEnd and add a check on lint method
 * the same way the other rules are called.
 */
public abstract class KlintRule {

	protected Definition javaDef;
	protected org.kframework.kil.loader.Context context;
	public abstract void run();
	
	public KlintRule(Context context) {
		this.context = context;
	}

	//TODO: Move to Definition?
	protected ArrayList<Rule> getRules(){
		ArrayList<Rule> rules = new ArrayList<Rule>();
		for(DefinitionItem di : this.javaDef.getItems()){
			if((di instanceof Module) && !((Module)di).isPredefined()){
				Module mod = (Module)di;
				for(ModuleItem mi : mod.getItems()){
					if(mi instanceof Rule){
						rules.add((Rule)mi);
					}
				}
			}
		}
		return rules;
	}

	//TODO: Move to Definition?
	protected ArrayList<Production> getProductions(){
		ArrayList<Production> productions = new ArrayList<Production>();

		for(DefinitionItem di : this.javaDef.getItems()){
			if((di instanceof Module) && !((Module)di).isPredefined()){
				for(ModuleItem mi : ((Module)di).getItems()){
					if(mi instanceof Syntax){
						for(PriorityBlock block : ((Syntax)mi).getPriorityBlocks()){
							for(Production production : block.getProductions()){
								productions.add(production);
							}
						}
					}
				}
			}
		}
		return productions;
	}


	/**
	 * Returns all rule that have a collection as body.
	 *
	 * @return A list of collections
	 */
	protected ArrayList<Collection> getRuleCollections(){
		ArrayList<Collection> collections = new ArrayList<Collection>();
		ArrayList<Rule> rules = getRules();
		for(Rule rule : rules){
			if(rule.getBody() instanceof Collection){
				Collection collection = (Collection)rule.getBody();
				collections.add(collection);
			}
		}
		return collections;
	}

	/**
	 * Get all rewrites from javaDef attribute.
	 *
	 * @param deep set as true if wants to get the rewrites that might not be 
	 * completed as well, for example rewrites that are in a bag, since the
	 * rewrites in the right might use variables from the rewrites in the left.
	 *
	 * @return returns a list with all rewrite rules from javaDef attribute;
	 */
	protected ArrayList<Rewrite> getRewrites(boolean deep){
		ArrayList<Rewrite> rewrites = new ArrayList<Rewrite>();
		ArrayList<Rule> rules = getRules();
		for(Rule rule : rules){
			if(rule.getBody() instanceof Rewrite){
				Rewrite rewrite = (Rewrite)rule.getBody();
				rewrites.add(rewrite);
				rewrites.addAll(getRewrites(rewrite));
			}
			else if(rule.getBody() instanceof Cell){
				Cell cell = (Cell)rule.getBody();
				rewrites.addAll(getRewrites(cell));
			}
			else if(deep && (rule.getBody() instanceof Collection)){
				Collection collection = (Collection)rule.getBody();
				rewrites.addAll(getRewrites(collection));
			}

		}
		return rewrites;
	}

	/**
	 * Get all recursive rewrites from the left or the right of a giving rewrite.
	 *
	 * @params rewrite the rewrite rule to be taken
	 * @return returns a list with all rewrite rules that are in this rewrite;
	 */
	private ArrayList<Rewrite> getRewrites(Rewrite rewrite){
		ArrayList<Rewrite> rewrites = new ArrayList<Rewrite>();
		rewrites.addAll(getRewrites(rewrite.getLeft()));
		rewrites.addAll(getRewrites(rewrite.getRight()));
		return rewrites;
	}


	/**
	 * Get all rewrites from a giving term.
	 *
	 * @params term the term that will be searched for rewrites.
	 * @return returns a list with all rewrite rules that are in this term;
	 */
	private ArrayList<Rewrite> getRewrites(Term term){
		ArrayList<Rewrite> rewrites = new ArrayList<Rewrite>();

		if(term instanceof Rewrite){
			rewrites.add((Rewrite)term);
			rewrites.addAll(getRewrites((Rewrite)term));
		}
		else if(term instanceof Collection){
			Collection collection = (Collection)term;
			for(Term t : collection.getContents()){
				rewrites.addAll(getRewrites(t));
			}
		}
		else if(term instanceof TermCons){
			TermCons termCons = (TermCons)term;
			for(Term t : termCons.getContents()){
				rewrites.addAll(getRewrites(t));
			}
		}
		else if(term instanceof Cell){
			Cell cell = (Cell)term;
			rewrites.addAll(getRewrites(cell.getContents()));
		}
		return rewrites;
	}

	/**
	 * Given a list of variables, deletes all anonymous variables from it
	 * @param vars the list of variables
	 * @return a new list without the anonymous variables
	 */
	protected static ArrayList<Variable> deleteAnonymous(ArrayList<Variable> vars) {
		ArrayList<Variable> result = new ArrayList<Variable>();
		for(Variable var : vars){
			if(var.getName().charAt(0) != '_' ){
			//if(!var.isAnonymous()){
				result.add(var);
			}
		}
		return result;
	}

	protected void warning(String message, ASTNode node){
		System.out.println(message + node);
	}
}

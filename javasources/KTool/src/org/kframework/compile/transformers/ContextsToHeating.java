package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * Initially created by Traian Florin Serbanuta
 * Date: 10/31/12
 * Time: 11:46 PM
 */
public class ContextsToHeating extends CopyOnWriteTransformer {
    private List<ModuleItem> rules = new ArrayList<ModuleItem>();
    
    public ContextsToHeating() {
           super("Contexts to Heating Rules");
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
    	return ((Module)super.transform(node)).addModuleItems(rules);
    }
    
    /* assumes term has exactly one rewrite and returns the list 
     * C[v], v, t1, t2 such that
     * v is a fresh variable and term= C[t1 => t2] */
    private List<Term> splitRewrite(Term term) throws TransformerException {
    	final Variable v = MetaK.getFreshVar("K");
    	final List<Term> list = new ArrayList<Term>();
    	Transformer transformer = new CopyOnWriteTransformer("splitter") {
    		@Override public ASTNode transform(Rewrite rewrite) {
    			list.add(rewrite.getLeft());
    			list.add(rewrite.getRight());
    			return v;
    		}
    	};
    	Term result = (Term)term.accept(transformer); 
    	list.add(0, v);
    	list.add(0, result);
    	return list;
    }
    
    private Term substituteHole(Term term, Term replacement) throws TransformerException {
		HashMap<Term, Term> hashMap = new HashMap<Term, Term>();
		hashMap.put(new Hole("K"), replacement);
		Substitution substitution = new Substitution(hashMap);
		if (term == null) {
			return null;
		}
		return (Term)term.accept(substitution);
    }

    private Term substituteVariable(Term term, Variable variable, Term replacement) throws TransformerException {
		HashMap<Term, Term> hashMap = new HashMap<Term, Term>();
		hashMap.put(variable, replacement);
		Substitution substitution = new Substitution(hashMap);
		if (term == null) {
			return null;
		}
		return (Term)term.accept(substitution);
    }

    @Override
    public ASTNode transform(Context node) throws TransformerException {
    	Term body = node.getBody();
    	Integer countRewrites = MetaK.countRewrites(body); 
    	if (countRewrites > 1) {
    		GlobalSettings.kem.register(
    				new KException(ExceptionType.ERROR,
    						KExceptionGroup.CRITICAL,
    						"Contexts can contain at most one rewrite",
    						getName(),
    						node.getLocation(),
    						node.getFilename()));
    	} else if (countRewrites == 0) {
    		body = substituteHole(body, new Rewrite(new Hole("K"), new Hole("K")));
    	}
    	List<Term> r = splitRewrite(body);
    	Term rewriteContext = r.get(0);
    	Variable freshVariable = (Variable)r.get(1);
    	Term left = r.get(2);
    	Term right = r.get(3);
    	if (!(left instanceof Hole)) {
    		GlobalSettings.kem.register(
    				new KException(ExceptionType.ERROR,
    						KExceptionGroup.CRITICAL,
    						"Only the HOLE can be rewritten in a context definition",
    						getName(),
    						node.getLocation(),
    						node.getFilename()));
    	}
    	Term lhsHeat = rewriteContext;
    	List<Term> rewriteList = new ArrayList<Term>();
    	rewriteList.add(substituteHole(right, freshVariable));
    	rewriteList.add(new Freezer(substituteVariable(rewriteContext, freshVariable, new FreezerHole(0))));
    	Term rhsHeat = new KSequence(rewriteList);
    	Rule heatingRule = new Rule(lhsHeat, rhsHeat);
    	heatingRule.setCondition(substituteHole(node.getCondition(), freshVariable));
    	heatingRule.putAttribute(MetaK.Constants.heatingTag,"");
    	rules.add(heatingRule);
    	
    	Rule coolingRule = new Rule(rhsHeat, lhsHeat);
    	coolingRule.putAttribute(MetaK.Constants.coolingTag,"");
    	rules.add(coolingRule);
    	
    	return null;
    }

    @Override
    public ASTNode transform(Syntax node) {
        return node;
    }

    @Override
    public ASTNode transform(Rule node) {
        return node;
    }

    @Override
    public ASTNode transform(Configuration node) {
        return node;
    }
}

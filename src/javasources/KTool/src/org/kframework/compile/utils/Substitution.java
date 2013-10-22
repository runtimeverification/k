package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Map;


public class Substitution extends CopyOnWriteTransformer {
	Map<Term, Term> substitution;
	public Substitution(Map<Term, Term> substitution, Context context) {
		super("Substitution", context);
		this.substitution = substitution;
	}
	
	@Override
	public ASTNode transform(Term node) throws TransformerException {
		Term substitute = substitution.get(node);
		if (!(null ==substitute)) 
			node = substitute;
		return super.transform(node);
	}
}

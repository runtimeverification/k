package org.kframework.compile.utils;

import java.util.Map;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Term;
import org.kframework.visitors.CopyOnWriteTransformer;


public class Substitution extends CopyOnWriteTransformer {
	Map<Term, Term> substitution;
	public Substitution(Map<Term, Term> substitution) {
		super("Substitution");
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

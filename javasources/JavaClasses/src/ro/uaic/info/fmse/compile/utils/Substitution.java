package ro.uaic.info.fmse.compile.utils;

import java.util.Map;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

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

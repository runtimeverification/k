package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.Iterator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.ListOfK;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class ResolveListOfK extends CopyOnWriteTransformer {

	public ResolveListOfK() {
		super("Resolve ListOfK");
	}
	
	
	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		boolean change = false;
		ArrayList<Term> terms = new ArrayList<Term>();
		Production prod = DefinitionHelper.conses.get(node.getCons());
		Iterator<Term> termIt = node.getContents().iterator();
		Term t;
		for (ProductionItem pitem : prod.getItems()) {
			if (pitem.getType() == ProductionType.TERMINAL) continue;
			t = termIt.next();
			ASTNode resultAST = t.accept(this);
			if (resultAST != t) change = true;
			if (resultAST != null) {
				if (!(resultAST instanceof Term)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting Term, but got " + resultAST.getClass() 
							+ " while transforming.", 
							t.getFilename(), t.getLocation()));					
				}
				Term result = (Term) resultAST;
				if (pitem instanceof Sort 
						&& ((Sort)pitem).getName().equals("List{K}") 
						&& !t.getSort().equals("List{K}")) {
					ListOfK list = new ListOfK();
					list.getContents().add(result);
					result = list;
					change = true;
				} 
				terms.add(result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setContents(terms);
		}
		return transform((Term) node);
	}

}

package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.visitors.BasicHookWorker;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CorrectKSeqFilter extends BasicTransformer {
	private CorrectKSeqFilter2 secondFilter = new CorrectKSeqFilter2();

	public CorrectKSeqFilter() {
		super("Correct K sequences");
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		if (tc.getProduction() == null)
			System.err.println(this.getClass() + ":" + " cons not found." + tc.getCons());
		if (tc.getProduction().isListDecl()) {
			tc.getContents().set(0, (Term) tc.getContents().get(0).accept(secondFilter));
			tc.getContents().set(1, (Term) tc.getContents().get(1).accept(secondFilter));
		} else if (!tc.getProduction().isConstant() && !tc.getProduction().isSubsort()) {
			for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
				if (tc.getProduction().getItems().get(i).getType() == ProductionType.SORT) {
					// look for the outermost element
					if (i == 0 || i == tc.getProduction().getItems().size() - 1) {
						tc.getContents().set(j, (Term) tc.getContents().get(j).accept(secondFilter));
					}
					j++;
				}
			}
		}

		return super.transform(tc);
	}

	/**
	 * A new class (nested) that goes down one level (jumps over Ambiguity) and checks to see if there is a KSequence
	 * 
	 * if found, throw an exception and until an Ambiguity node catches it
	 * 
	 * @author Radu
	 * 
	 */
	public class CorrectKSeqFilter2 extends BasicHookWorker {
		public CorrectKSeqFilter2() {
			super("org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter2");
		}

		public ASTNode transform(KSequence ks) throws TransformerException {
			String msg = "Due to typing errors, ~> is not greedy. Use parentheses to set proper scope.";
			KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getFilename(), ks.getLocation());
			throw new PriorityException(kex);
		}

		@Override
		public ASTNode transform(Ambiguity node) throws TransformerException {
			TransformerException exception = null;
			ArrayList<Term> terms = new ArrayList<Term>();
			for (Term t : node.getContents()) {
				ASTNode result = null;
				try {
					result = t.accept(this);
					terms.add((Term) result);
				} catch (TransformerException e) {
					exception = e;
				}
			}
			if (terms.isEmpty())
				throw exception;
			if (terms.size() == 1) {
				return terms.get(0);
			}
			node.setContents(terms);
			return node;
		}
	}
}

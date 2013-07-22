package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicHookWorker;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CellTypesFilter extends BasicTransformer {

	public CellTypesFilter(org.kframework.kil.loader.Context context) {
		super("Cell types", context);
	}

	// don't do anything for configuration and syntax
	public ASTNode transform(Configuration cell) {
		return cell;
	}

	public ASTNode transform(Syntax cell) {
		return cell;
	}

	public ASTNode transform(Cell cell) throws TransformerException {
		String sort = context.cellKinds.get(cell.getLabel());

		if (sort == null) {
			if (cell.getLabel().equals("k"))
				sort = "K";
			else if (cell.getLabel().equals("T"))
				sort = "Bag";
			else if (cell.getLabel().equals("generatedTop"))
				sort = "Bag";
			else if (cell.getLabel().equals("freshCounter"))
				sort = "K";
			else if (cell.getLabel().equals(MetaK.Constants.pathCondition))
				sort = "K";
		}

		if (sort != null) {
			cell.setContents((Term) cell.getContents().accept(new CellTypesFilter2(context, sort, cell.getLabel())));
		} else {
			String msg = "Cell '" + cell.getLabel() + "' was not declared in a configuration.";
			throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), cell.getFilename(), cell.getLocation()));
		}
		return super.transform(cell);
	}

	/**
	 * A new class (nested) that goes down one level (jumps over Ambiguity) and checks to see if there is a KSequence
	 * 
	 * if found, throw an exception and until an Ambiguity node catches it
	 * 
	 * @author Radu
	 * 
	 */
	public class CellTypesFilter2 extends BasicHookWorker {
		String expectedSort;
		String cellLabel;

		public CellTypesFilter2(Context context, String expectedSort, String cellLabel) {
			super("org.kframework.parser.concrete.disambiguate.CellTypesFilter2", context);
			this.expectedSort = expectedSort;
			this.cellLabel = cellLabel;
		}

		public ASTNode transform(Term trm) throws TransformerException {
			if (!context.isSubsortedEq(expectedSort, trm.getSort())) {
				// if the found sort is not a subsort of what I was expecting
				String msg = "Wrong type in cell '" + cellLabel + "'. Expected sort: " + expectedSort + " but found " + trm.getSort();
				throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), trm.getFilename(), trm.getLocation()));
			}
			return trm;
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

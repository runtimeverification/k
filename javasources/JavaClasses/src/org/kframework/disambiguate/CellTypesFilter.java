package org.kframework.disambiguate;

import java.util.ArrayList;
import java.util.List;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Ambiguity;
import org.kframework.k.Cell;
import org.kframework.k.Configuration;
import org.kframework.k.Syntax;
import org.kframework.k.Term;
import org.kframework.loader.DefinitionHelper;
import org.kframework.visitors.BasicTransformer;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class CellTypesFilter extends BasicTransformer {

	public CellTypesFilter() {
		super("Cell types");
		// TODO Auto-generated constructor stub
	}

	// don't do anything for configuration and syntax
	public ASTNode transform(Configuration cell) {
		return cell;
	}

	public ASTNode transform(Syntax cell) {
		return cell;
	}

	public ASTNode transform(Cell cell) throws TransformerException {
		String sort = DefinitionHelper.cells.get(cell.getLabel());

		if (sort != null) {
			if (cell.getContents() instanceof Ambiguity) {
				List<Term> children = new ArrayList<Term>();
				for (Term t : ((Ambiguity) cell.getContents()).getContents()) {
					if (DefinitionHelper.isSubsortedEq(sort, t.getSort()))
						children.add(t);
				}

				if (children.size() == 0) {
					cell.setContents(((Ambiguity) cell.getContents()).getContents().get(0));
				} else if (children.size() == 1) {
					cell.setContents(children.get(0));
				} else {
					((Ambiguity) cell.getContents()).setContents(children);
				}
			}

			if (!(cell.getContents() instanceof Ambiguity))
				if (!DefinitionHelper.isSubsortedEq(sort, cell.getContents().getSort())) {
					// if the found sort is not a subsort of what I was expecting
					String msg = "Wrong type in cell '" + cell.getLabel() + "'. Expected sort: " + sort + " but found " + cell.getContents().getSort();
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, cell.getFilename(), cell.getLocation(), 0));
				}
		} else
			; // TODO: should give warning saying that the cell was not declared
		return super.transform(cell);
	}
}

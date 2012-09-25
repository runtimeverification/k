package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class CellTypesFilter extends BasicTransformer {

	public CellTypesFilter() {
		super("Cell types");
	}

	// don't do anything for configuration and syntax
	public ASTNode transform(Configuration cell) {
		return cell;
	}

	public ASTNode transform(Syntax cell) {
		return cell;
	}

	public ASTNode transform(Cell cell) throws TransformerException {
		String sort = DefinitionHelper.cellSorts.get(cell.getLabel());

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
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, cell.getFilename(), cell.getLocation()));
				}
		} else {
			String msg = "Cell '" + cell.getLabel() + "' was not declared in a configuration.";
			GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.COMPILER, msg, cell.getFilename(), cell.getLocation()));
		}
		return super.transform(cell);
	}
}

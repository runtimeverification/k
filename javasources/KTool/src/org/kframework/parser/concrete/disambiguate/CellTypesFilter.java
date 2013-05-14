package org.kframework.parser.concrete.disambiguate;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.List;

public class CellTypesFilter extends BasicTransformer {

	public CellTypesFilter(DefinitionHelper definitionHelper) {
		super("Cell types", definitionHelper);
	}

	// don't do anything for configuration and syntax
	public ASTNode transform(Configuration cell) {
		return cell;
	}

	public ASTNode transform(Syntax cell) {
		return cell;
	}

	public ASTNode transform(Cell cell) throws TransformerException {
		String sort = definitionHelper.cellSorts.get(cell.getLabel());

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
			if (cell.getContents() instanceof Ambiguity) {
				List<Term> children = new ArrayList<Term>();
				for (Term t : ((Ambiguity) cell.getContents()).getContents()) {
					if (definitionHelper.isSubsortedEq(sort, t.getSort(definitionHelper)))
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
				if (!definitionHelper.isSubsortedEq(sort, cell.getContents().getSort(definitionHelper))) {
					// if the found sort is not a subsort of what I was expecting
					String msg = "Wrong type in cell '" + cell.getLabel() + "'. Expected sort: " + sort + " but found " + cell.getContents().getSort(definitionHelper);
					throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), cell.getFilename(), cell.getLocation()));
				}
		} else {
			String msg = "Cell '" + cell.getLabel() + "' was not declared in a configuration.";
			throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), cell.getFilename(), cell.getLocation()));
		}
		return super.transform(cell);
	}
}

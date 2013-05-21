package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CellEndLabelFilter extends BasicTransformer {

	public CellEndLabelFilter(Context context) {
		super("Cell End Label", context);
	}

	public ASTNode transform(Syntax cell) {
		return cell;
	}

	public ASTNode transform(Cell cell) throws TransformerException {
		if (!cell.getLabel().equals(cell.getEndLabel())) {
			String msg = "Cell starts with '" + cell.getLabel() + "' but ends with '" + cell.getEndLabel() + "'";
			// String msg = "Variable " + r.getName() + " cannot have sort " + r.getSort() + " at this location. Expected sort " + correctSort + ".";
			KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, cell.getFilename(), cell.getLocation());
			throw new TransformerException(kex);
		}
		return super.transform(cell);
	}
}

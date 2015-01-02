// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CellEndLabelFilter extends ParseForestTransformer {

    public CellEndLabelFilter(Context context) {
        super("Cell End Label", context);
    }

    @Override
    public ASTNode visit(Syntax cell, Void _void) {
        return cell;
    }

    @Override
    public ASTNode visit(Cell cell, Void _void) throws ParseFailedException {
        if (!cell.getLabel().equals(cell.getEndLabel())) {
            String msg = "Cell starts with '" + cell.getLabel() + "' but ends with '" + cell.getEndLabel() + "'";
            // String msg = "Variable " + r.getName() + " cannot have sort " + r.getSort() + " at this location. Expected sort " + correctSort + ".";
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, cell.getSource(), cell.getLocation());
            throw new ParseFailedException(kex);
        }
        return super.visit(cell, _void);
    }
}

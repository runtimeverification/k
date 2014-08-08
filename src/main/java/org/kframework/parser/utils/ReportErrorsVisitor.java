// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Location;
import org.kframework.kil.ParseError;
import org.kframework.kil.Source;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class ReportErrorsVisitor extends ParseForestTransformer {
    String fromWhere = null;

    public ReportErrorsVisitor(Context context, String fromWhere) {
        super("Report parse errors", context);
        this.fromWhere = fromWhere;
    }

    public ASTNode visit(ParseError pe, Void _) throws ParseFailedException {
        String msg = pe.getMessage();
        if (msg.equals("Parse error: eof unexpected"))
            msg = "Parse error: Unexpected end of " + fromWhere;
        Source source = pe.getSource();
        Location location = pe.getLocation();
        throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, source, location));
    }
}

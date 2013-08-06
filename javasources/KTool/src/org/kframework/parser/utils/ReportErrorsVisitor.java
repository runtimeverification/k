package org.kframework.parser.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.ParseError;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class ReportErrorsVisitor extends BasicTransformer {
	String fromWhere = null;

	public ReportErrorsVisitor(Context context, String fromWhere) {
		super("Report parse errors", context);
		this.fromWhere = fromWhere;
	}

	public ASTNode transform(ParseError pe) throws TransformerException {
		String msg = pe.getMessage();
		if (msg.equals("Parse error: eof unexpected"))
			msg = "Parse error: Unexpected end of " + fromWhere;
		String file = pe.getFilename();
		String location = pe.getLocation();
		throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, file, location));
	}
}

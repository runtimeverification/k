package org.kframework.kcheck.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class RemoveLabel extends CopyOnWriteTransformer {

	public final String LABEL = "program-label";
	
	public RemoveLabel(Context context) {
		super("Remove the program klabel", context);
	}

	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		
		if (node.getProduction().containsAttribute(LABEL)) {
			Term stmt = node.getContents().get(node.getContents().size() - 1);
			return stmt;
		}
		
		return super.transform(node);
	}
}

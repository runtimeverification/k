package org.kframework.compile.tags;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddStrictStar extends BasicTransformer{

	public AddStrictStar() {
		super("AddStrictStar");
	}

	@Override
	public ASTNode transform(Production node) throws TransformerException {
		if (node.containsAttribute("strict") || node.containsAttribute("seqstrict"))
			node.putAttribute("strict*", "");
		
		return node;
	}
}

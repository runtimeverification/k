package org.kframework.compile.tags;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.Rule;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddDefaultComputational extends BasicTransformer{

	public AddDefaultComputational() {
		super("AddDefaultComputational");
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		
		Attributes attributes = node.getAttributes();
		if (!(attributes.containsKey("structural") || attributes.containsKey("anywhere")))
			attributes.set("computational", "");
		
		return node;
	}
}

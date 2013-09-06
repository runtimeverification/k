package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/** An import directive */
public class Import extends ModuleItem {

	String name;

	public Import(String importName) {
		super();
		name = importName;
	}

	public Import(Import import1) {
		super(import1);
		this.name = import1.name;
	}

	@Override
	public String toString() {
		return "  imports " + name;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	@Override
	public Import shallowCopy() {
		return new Import(this);
	}
}

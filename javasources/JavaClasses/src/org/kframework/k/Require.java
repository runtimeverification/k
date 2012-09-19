package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.loader.Constants;
import org.kframework.visitors.Modifier;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Element;


public class Require extends DefinitionItem {
	private String value;

	public Require(Element element) {
		super(element);
		value = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public Require(Require require) {
		super(require);
		value = require.value;
	}

	@Override
	public String toMaude() {
		return "";
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	public void setValue(String value) {
		this.value = value;
	}

	public String getValue() {
		return value;
	}

	@Override
	public Require shallowCopy() {
		return new Require(this);
	}
}

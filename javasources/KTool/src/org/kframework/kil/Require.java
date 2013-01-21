package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

/** A require directive */
public class Require extends DefinitionItem {
	/** The string argument to {@code require}, as written in the input file. */
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
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

  @Override
  public void accept(Matcher matcher, ASTNode toMatch){
    matcher.match(this, toMatch);
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

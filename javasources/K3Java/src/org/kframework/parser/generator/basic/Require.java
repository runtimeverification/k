package org.kframework.parser.generator.basic;

import org.kframework.kil.loader.Constants;
import org.w3c.dom.Element;
import org.w3c.dom.Node;


public class Require extends ModuleItem implements Cloneable {
	private String value;
	private boolean predefined = false;

	public Require clone() {
		return this;
	}

	public Require() {
	}

	public Require(Node require) {
		super(require);

		this.setValue(((Element) require).getAttribute(Constants.VALUE_value_ATTR));
	}

	public void setPredefined(boolean predefined) {
		this.predefined = predefined;
		Element elm = (Element) this.xmlTerm;
		elm.setAttribute("predefined", predefined + "");
	}

	public boolean isPredefined() {
		return predefined;
	}

	@Override
	public ModuleType getType() {
		return ModuleType.REQUIRE;
	}

	public void setValue(String value) {
		this.value = value;
	}

	public String getValue() {
		return value;
	}
}

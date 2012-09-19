package org.kframework.kil;

import java.util.LinkedList;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


public class Attribute extends ASTNode {

	private String key;
	private String value;

	public Attribute(String key, String value) {
		super();
		this.key = key;
		this.value = value;
	}

	public Attribute(Element elm) {
		super(elm);

		key = elm.getAttribute(Constants.KEY_key_ATTR);
		value = elm.getAttribute(Constants.VALUE_value_ATTR);
	}

	public Attribute(Attribute attribute) {
		super(attribute);
		key = attribute.key;
		value = attribute.value;
	}

	@Override
	public String toMaude() {
		java.util.List<String> reject = new LinkedList<String>();
		reject.add("cons");
		reject.add("kgeneratedlabel");
		reject.add("latex");
		reject.add("prefixlabel");

		if (!reject.contains(this.getKey()))
			return " " + this.getKey() + "=(" + this.getValue() + ")";

		return "";
	}

	@Override
	public String toString() {
	    return " " + this.getKey() + "=(" + this.getValue() + ")";
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);

	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException  {
		return visitor.transform(this);
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	public void setValue(String value) {
		this.value = value;
	}

	public String getValue() {
		return value;
	}

	public void setKey(String key) {
		this.key = key;
	}

	public String getKey() {
		return key;
	}
	
	@Override
	public Attribute shallowCopy() {
		return new Attribute(this);
	}
}

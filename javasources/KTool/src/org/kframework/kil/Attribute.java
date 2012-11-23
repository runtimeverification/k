package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

public class Attribute extends ASTNode {

    /*
    public enum AttributeKey {
        PREDICATE_KEY("predicate");

        private String key;
        AttributeKey(String key) {
            this.key = key;
        }
    }
    */

    public static final String FUNCTION_KEY = "function";
    public static final String PREDICATE_KEY = "predicate";
    public static final String ANYWHERE_KEY = "anywhere";
    public static final String BRACKET_KEY = "bracket";
    public static final String BINDER_KEY = "binder";

    public static final Attribute FUNCTION = new Attribute(FUNCTION_KEY, "");
    public static final Attribute PREDICATE = new Attribute(PREDICATE_KEY, "");


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
	public String toString() {
		return " " + this.getKey() + "=(" + this.getValue() + ")";
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

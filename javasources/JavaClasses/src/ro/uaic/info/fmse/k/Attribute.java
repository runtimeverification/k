package ro.uaic.info.fmse.k;

import java.util.LinkedList;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Attribute extends ASTNode {

	private String key;
	private String value;

	public Attribute(String key, String value) {
		super("generated", "generated");
		this.key = key;
		this.value = value;
	}

	public Attribute(Element elm) {
		super(elm);

		key = elm.getAttribute(Constants.KEY_key_ATTR);
		value = elm.getAttribute(Constants.VALUE_value_ATTR);
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
	public Element toXml(Document doc) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);

	}

	@Override
	public ASTNode accept(Transformer visitor) {
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
}

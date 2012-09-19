package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


public class Configuration extends Sentence {

	public Configuration() {
		super("File System", "generated");
	}
	
	public Configuration(String location, String filename) {
		super(location, filename);
	}

	public Configuration(Element element) {
		super(element);
	}

	public Configuration(Configuration node) {
		super(node);
	}

	public String toString() {
		String content = "  configuration ";
		content += this.body + " ";
		return content;
	}

	@Override
	public String toMaude() {
		return "mb configuration " + super.toMaude();
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
	public Configuration shallowCopy() {
		return new Configuration(this);
	}
}

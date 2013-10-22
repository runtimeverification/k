package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/**
 * Configuration declaration.
 * The term {@code body} is the intial configuration as a bag of cells,
 * also allowing cell attributes and variables such as {@code $PGM}. 
 * May not have a non-null {@code condition}.
 */
public class Configuration extends Sentence {

	public Configuration() {
		super();
	}

	public Configuration(Element element) {
		super(element);
	}

	public Configuration(ATermAppl element) {
		super(element);
	}

	public Configuration(Configuration node) {
		super(node);
	}

	public Configuration(Sentence term) {
		super(term);
	}

	public String toString() {
		String content = "  configuration ";
		content += this.body + " ";
		return content;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public Configuration shallowCopy() {
		return new Configuration(this);
	}
}

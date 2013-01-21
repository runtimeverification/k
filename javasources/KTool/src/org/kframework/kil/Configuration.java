package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.spoofax.interpreter.terms.IStrategoAppl;
import org.w3c.dom.Element;

/**
 * Configuration declaration.
 * The term {@code body} is the intial configuration as a bag of cells,
 * also allowing cell attributes and variables such as {@code $PGM}. 
 * May not have a non-null {@code condition}.
 */
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

	public Configuration(IStrategoAppl element) {
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

	@Override
	public Configuration shallowCopy() {
		return new Configuration(this);
	}
}

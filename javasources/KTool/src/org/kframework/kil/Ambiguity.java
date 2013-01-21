package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

/** Used for representing parsing ambiguity.
 * Shouldn't exist after disambiguation. 
 */
public class Ambiguity extends Collection {

	public Ambiguity(Element element) {
		super(element);
	}

	public Ambiguity(Ambiguity node) {
		super(node);
	}

	public Ambiguity(String sort, java.util.List<Term> col) {
		super(sort, col);
	}

	@Override
	public String toString() {
		String content = "";

		for (Term term : contents)
			if (term != null)
				content += term + ",";

		if (content.length() > 1)
			content = content.substring(0, content.length() - 1);

		return "amb(" + content + ")";
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
	public Ambiguity shallowCopy() {
		return new Ambiguity(this);
	}
}

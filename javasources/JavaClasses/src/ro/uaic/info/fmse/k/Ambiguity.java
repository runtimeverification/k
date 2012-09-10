package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Ambiguity extends Collection {

	public Ambiguity(Element element) {
		super(element);
	}

	public Ambiguity(Ambiguity node) {
		super(node);
	}

	@Override
	public String toMaude() {
		String content = "";

		for (Term term : contents)
			if (term != null)
				content += term.toMaude() + ",";

		if (content.length() > 1)
			content = content.substring(0, content.length() - 1);

		return "amb(" + content + ")";
	}

	@Override
	public Element toXml(Document doc) {
		return null;
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
	public Ambiguity shallowCopy() {
		return new Ambiguity(this);
	}
}

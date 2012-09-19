package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


public class KSequence extends Collection {
	public KSequence(Element element) {
		super(element);
	}

	public KSequence(KSequence node) {
		super(node);
	}

	@Override
	public String toString() {
		String content = "";
		for (int i = 0; i < contents.size(); i++) {
			if (i == contents.size() -1)
				content += contents.get(i);
			else
				content += contents.get(i) + "~> ";
		}
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
	public KSequence shallowCopy() {
		return new KSequence(this);
	}
}

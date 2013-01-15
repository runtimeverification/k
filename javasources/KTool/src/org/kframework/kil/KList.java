package org.kframework.kil;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import java.util.List;

public class KList extends Collection {
	public KList() {
		super(MetaK.Constants.KList);
	}
	
	public KList(String location, String filename) {
		super(location, filename, MetaK.Constants.KList);
	}

	public KList(Element element) {
		super(element);
	}

	public KList(KList node) {
		super(node);
	}

	public KList(List<Term> col) {
		super(MetaK.Constants.KList, col);
	}

	@Override
	public String toString() {
		String content = "";
		for (int i = 0; i < contents.size(); i++) {
			if (i == contents.size() - 1)
				content += contents.get(i);
			else
				content += contents.get(i) + ",, ";
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
	public KList shallowCopy() {
		return new KList(this);
	}
}

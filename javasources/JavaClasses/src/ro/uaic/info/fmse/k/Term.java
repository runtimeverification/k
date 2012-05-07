package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.ASTNode;

public abstract class Term extends ASTNode {
	public Term(Element element) {
		super(element);
	}

	@Override
	public String toMaude() {
		return "";
	}

	@Override
	public Element toXml(Document doc) {
		Element term = doc.createElement(Constants.TERM);
		return term;
	}
}

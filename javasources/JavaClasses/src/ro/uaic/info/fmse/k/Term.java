package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.ASTNode;

public abstract class Term extends ASTNode {
	String sort;

	public Term(String location, String filename, String sort) {
		super(location, filename);
		this.sort = sort;
	}

	public Term(String location, String filename) {
		super(location, filename);
	}

	public Term(Element element) {
		super(element);
	}

	@Override
	public Element toXml(Document doc) {
		Element term = doc.createElement(Constants.TERM);
		return term;
	}
}

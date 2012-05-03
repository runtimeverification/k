package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.ASTNode;

public abstract class Term extends ASTNode {
	public Term(Element element) {
		super(element);
	}
}

package k3.basic;

import org.w3c.dom.Node;

public abstract class Sentence extends Term {
	public enum SentenceType {
		RULE, CONFIGURATION, CONTEXT, INCLUDING, SYNTAX, COMMENT;
	}

	public Sentence() {
	}

	public Sentence(Sentence s) {
		super(s);
	}

	public Sentence(Node node) {
		super(node);
	}

	public SentenceType getType() {
		return null;
	}

	@Override
	public Sentence clone() {
		return null;
	}
}

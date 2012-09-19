package org.kframework.parser.generator.basic;

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

	public abstract SentenceType getType();

	@Override
	public Sentence clone() {
		return null;
	}
}

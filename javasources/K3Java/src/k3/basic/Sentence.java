package k3.basic;

public abstract class Sentence extends Term {
	public enum SentenceType {
		RULE, CONFIGURATION, CONTEXT, INCLUDING, SYNTAX, DEFINE;
	}

	public SentenceType getType() {
		return null;
	}

	@Override
	public Sentence clone() {
		return null;
	}
}

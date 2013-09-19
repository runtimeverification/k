package org.kframework.kil;

public interface LiterateComment {
	public enum LiterateCommentType {
		LATEX, PREAMBLE, COMMON;
		public String toString() {
			if (this == LATEX) { return "@"; }
			else if (this == PREAMBLE) { return "!"; }
			else { assert this == COMMON; return ""; }
		}
	}

	public LiterateCommentType getType();
}

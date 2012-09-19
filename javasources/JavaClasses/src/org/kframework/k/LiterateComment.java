package org.kframework.k;

public interface LiterateComment {
	public enum LiterateCommentType {
		LATEX, PREAMBLE, COMMON
	};

	public LiterateCommentType getType();
}

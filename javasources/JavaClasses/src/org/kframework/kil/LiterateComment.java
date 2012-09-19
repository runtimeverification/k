package org.kframework.kil;

public interface LiterateComment {
	public enum LiterateCommentType {
		LATEX, PREAMBLE, COMMON
	};

	public LiterateCommentType getType();
}

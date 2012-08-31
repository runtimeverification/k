package ro.uaic.info.fmse.k;

public interface LiterateComment {
	public enum LiterateCommentType {
		LATEX, PREAMBLE, COMMON
	};

	public LiterateCommentType getType();
}

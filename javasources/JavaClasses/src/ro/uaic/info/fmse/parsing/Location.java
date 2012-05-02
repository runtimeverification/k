package ro.uaic.info.fmse.parsing;

public class Location {
	String filename;
	int lineNumber;
	int columnNumber;
	int startOffset;
	int endOffset;
	
	public Location() {
		this.filename = "filename";
		this.columnNumber = 0;
		this.lineNumber = 0;
		this.startOffset = 0;
		this.endOffset = 0;
	}
}

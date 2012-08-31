package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

public class Location extends Attribute {
	public Location(Element elm) {
		super(elm);
	}
	String filename;
	int lineNumber;
	int columnNumber;
	int startOffset;
	int endOffset;
	
}

package k3.basic;

import org.w3c.dom.Node;

public abstract class Term implements Cloneable {
	protected String location, filename;
	protected Node xmlTerm;
	
	public void copy(Term t) {
		this.location = t.location;
		this.filename = t.filename;
		this.xmlTerm = t.xmlTerm;
	}

	public Node getXmlTerm() {
		return xmlTerm;
	}

	public void setXmlTerm(Node xmlTerm) {
		this.xmlTerm = xmlTerm;
	}

	public String getLocation() {
		return location;
	}

	public void setLocation(String location) {
		this.location = location;
	}

	public String getFilename() {
		return filename;
	}

	public void setFilename(String filename) {
		this.filename = filename;
	}
}

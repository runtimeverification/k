package k3.basic;

import k.utils.Tag;
import k.utils.XmlLoader;

import org.w3c.dom.Element;
import org.w3c.dom.Node;

public abstract class Term implements Cloneable {
	protected String location, filename;
	protected Node xmlTerm;

	public Term() {
		location = "generated";
		filename = "generated";
		xmlTerm = null;
	}

	public Term(Term term) {
		this.location = term.location;
		this.filename = term.filename;
		this.xmlTerm = term.xmlTerm;
	}

	public Term(Node node) {
		Element el = (Element) node;
		this.location = el.getAttribute(Tag.location);
		this.filename = el.getAttribute(Tag.filename);
		this.xmlTerm = node;
	}

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

	public int getStartLine() {
		return XmlLoader.getLocNumber(location, 0);
	}

	public int getEndLine() {
		return XmlLoader.getLocNumber(location, 2);
	}
}

package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Modifier;
import ro.uaic.info.fmse.parsing.Transformer;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class Attributes extends ASTNode {

	protected java.util.List<Attribute> contents;

	public Attributes(Attributes c) {
		super(c);
		this.contents = c.contents;
	}

	public Attributes(String location, String filename) {
		super(location, filename);
		contents = new ArrayList<Attribute>();
	}

	public Attributes(Element element) {
		super(element);

		contents = new LinkedList<Attribute>();
		List<Element> children = XML.getChildrenElements(element);
		for (Element e : children)
			contents.add((Attribute) JavaClassesFactory.getTerm(e));
	}

	@Override
	public String toString() {
		if (isEmpty())
			return "";
		String content = "[";
		for (Attribute t : contents)
			content += t + ", ";
		return content.substring(0, contents.size() - 2) + "]";
	}

	@Override
	public String toMaude() {
		String attributes = "";
		for (Attribute entry : contents) {
			attributes += entry.toMaude();
		}

		return attributes.trim();
	}

	public boolean containsKey(String key) {
		if (contents == null)
			return false;
		for (Attribute attr : contents)
			if (attr.getKey().equals(key))
				return true;
		return false;
	}

	public String get(String key) {
		for (Attribute attr : contents)
			if (attr.getKey().equals(key))
				return attr.getValue();
		return null;
	}

	public boolean isEmpty() {
		return this.contents.isEmpty();
	}

	public java.util.List<Attribute> getContents() {
		return contents;
	}

	public void setContents(java.util.List<Attribute> contents) {
		this.contents = contents;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		for (int i = 0; i < this.contents.size(); i++) {
			Attribute elem = (Attribute) visitor.modify(this.contents.get(i));
			this.contents.set(i, elem);
		}
	}

	@Override
	public Element toXml(Document doc) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
}

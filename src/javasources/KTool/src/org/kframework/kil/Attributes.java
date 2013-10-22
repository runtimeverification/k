package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * class for AST Attributes.
 * This is used to represent a collection of attributes on a node,
 * which may contain both attributes in the K source
 * written by a user, and metadata like location added by kompile.
 * Only {@link Rule} and {@link Production} may have user-written
 * attributes.
 *
 * @see ASTNode
 */
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

		contents = new ArrayList<Attribute>();
		List<Element> children = XML.getChildrenElements(element);
		for (Element e : children)
			contents.add((Attribute) JavaClassesFactory.getTerm(e));
	}

	public Attributes() {
		contents = new ArrayList<Attribute>();
	}

	@Override
	public String toString() {
		if (isEmpty())
			return "";
		String content = "[";
		for (Attribute t : contents)
			content += t + ", ";
		return content.substring(0, content.length() - 2) + "]";
	}

	public boolean containsKey(String key) {
		if (contents == null)
			return false;
		for (Attribute attr : contents)
			if (attr.getKey().equals(key))
				return true;
		return false;
	}

	public Attribute getAttributeByKey(String key) {
		for (Attribute attr : contents)
			if (attr.getKey().equals(key))
				return attr;
		return null;
	}

	public String get(String key) {
		for (Attribute attr : contents)
			if (attr.getKey().equals(key))
				return attr.getValue();
		return null;
	}

	public void set(String key, String value) {
		for (Attribute attr : contents) {
			if (attr.getKey().equals(key)) {
				attr.setValue(value);
				return;
			}
		}
		contents.add(new Attribute(key, value));
	}

    public void setAll(Attributes attrs) {
        for (Attribute attr : attrs.contents)
            set(attr);
    }

	public void set(Attribute attr) {
		Attribute oldAttr = getAttributeByKey(attr.getKey());
		if (oldAttr != null) {
			oldAttr.setValue(attr.getValue());
		} else {
			contents.add(attr);
		}

	}

	public void remove(String key) {
		Iterator<Attribute> it = contents.iterator();
		while(it.hasNext()){
			Attribute a = (Attribute) it.next();
			if(a.getKey().equals(key))
				it.remove();
		}
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
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public Attributes shallowCopy() {
		Attributes result = new Attributes();
		result.contents.addAll(contents);
		return result;
	}
}

package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/** MapItem is a map item with key {@link #key} and value the inherited {@link #value} */
public class MapItem extends CollectionItem {
	private Term key;

	public MapItem(Element element) {
		super(element);
		Element elm = XML.getChildrenElementsByTagName(element, Constants.KEY).get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.key = (Term) JavaClassesFactory.getTerm(elmBody);

		elm = XML.getChildrenElementsByTagName(element, Constants.VALUE).get(0);
		elmBody = XML.getChildrenElements(elm).get(0);
		this.value = (Term) JavaClassesFactory.getTerm(elmBody);
	}

	public MapItem(ATermAppl atm) {
		super(atm);
		key = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));
		value = (Term) JavaClassesFactory.getTerm(atm.getArgument(1));
	}

	public MapItem(String location, String filename) {
		super(location, filename, "MapItem");
	}

	public MapItem(MapItem node) {
		super(node);
		this.key = node.key;
	}

	public MapItem() {
		super("MapItem");
	}

	public MapItem(Term key, Term value) {
		this();
		this.key = key;
		this.value = value;
	}

	public void setKey(Term key) {
		this.key = key;
	}

	public Term getKey() {
		return key;
	}

	public Term getValue() {
		return value;
	}

	public void setValue(Term t) {
		value = t;
	}

	public String toString() {
		return this.key + " |->" + this.value;
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
	public void accept(Matcher matcher, Term toMatch) {
		matcher.match(this, toMatch);
	}

	@Override
	public MapItem shallowCopy() {
		return new MapItem(this);
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof MapItem))
			return false;
		MapItem m = (MapItem) o;
		return key.equals(m.key) && value.equals(m.value);
	}

	@Override
	public boolean contains(Object o) {
		if (o instanceof Bracket)
			return contains(((Bracket) o).getContent());
		if (o instanceof Cast)
			return contains(((Cast) o).getContent());
		if (!(o instanceof MapItem))
			return false;
		MapItem m = (MapItem) o;
		return key.contains(m.key) && value.contains(m.value);
	}

	@Override
	public int hashCode() {
		return key.hashCode() * 31 + value.hashCode();
	}
}

package org.kframework.kil;

import org.w3c.dom.Element;

import aterm.ATermAppl;

/** Subclasses wrap a term as an item in the corresponding collection */
public abstract class CollectionItem extends Term {

	protected Term value;

	public CollectionItem(CollectionItem i) {
		super(i);
		this.value = i.value;
	}

	public CollectionItem(String location, String filename, String sort) {
		super(location, filename, sort);
	}

	public CollectionItem(Element element) {
		super(element);
	}

	public CollectionItem(ATermAppl atm) {
		super(atm);
	}

	public CollectionItem(String sort) {
		super(sort);
	}

	public void setItem(Term value) {
		this.value = value;
	}

	public Term getItem() {
		return value;
	}

	@Override
	public abstract CollectionItem shallowCopy();

	@Override
	public boolean equals(Object o) {
		if (getClass() != o.getClass())
			return false;
		CollectionItem c = (CollectionItem) o;
		return sort.equals(c.sort) && value.equals(c.value);
	}

	@Override
	public boolean contains(Object o) {
		if (o instanceof Bracket)
			return contains(((Bracket) o).getContent());
		if (o instanceof Cast)
			return contains(((Cast) o).getContent());
		if (getClass() != o.getClass())
			return false;
		CollectionItem c = (CollectionItem) o;
		return sort.equals(c.sort) && value.contains(c.value);
	}

	@Override
	public int hashCode() {
		return sort.hashCode() * 19 + value.hashCode();
	}
}

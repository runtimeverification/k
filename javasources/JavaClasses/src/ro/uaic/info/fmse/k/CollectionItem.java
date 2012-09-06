package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

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

}
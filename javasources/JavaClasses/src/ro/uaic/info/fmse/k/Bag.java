package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

public class Bag extends Collection {
	public Bag(String location, String filename) {
		super(location, filename);
	}

	public Bag(Element element) {
		super(element);
	}

	@Override
	public String toString() {
		return super.toString();
	}
}
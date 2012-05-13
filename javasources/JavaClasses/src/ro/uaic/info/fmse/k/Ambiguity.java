package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class Ambiguity extends Collection {

	public Ambiguity(Element element) {
		super(element);
	}

	@Override
	public String toMaude() {
		return this.contents.get(0).toMaude();
	}

	@Override
	public Element toXml(Document doc) {
		return null;
	}
}

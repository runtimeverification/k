package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;


public class Predicate extends Sentence {

	public Predicate(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	@Override
	public Element toXml(Document doc) {
		Element predicate = doc.createElement(Constants.PREDICATE);
		predicate.setTextContent("notImplementedYet");
		return predicate;
	}
}

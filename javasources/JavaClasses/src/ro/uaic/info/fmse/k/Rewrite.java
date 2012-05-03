package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;


public class Rewrite extends Term {
	Term left;
	Term right;

	public Rewrite(Element element) {
		super(element);
		
		left = (Term) JavaClassesFactory.getTerm(XML.getChildrenElementsByTagName(element, Constants.LEFT).get(0));
		right = (Term) JavaClassesFactory.getTerm(XML.getChildrenElementsByTagName(element, Constants.RIGHT).get(0));
	}

	@Override
	public String toString() {
		return left + " => " + right;
	}
}

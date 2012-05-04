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
		
		Element temp = XML.getChildrenElementsByTagName(element, Constants.LEFT).get(0);
		temp = XML.getChildrenElements(temp).get(0);
		left = (Term) JavaClassesFactory.getTerm(temp);
		temp = XML.getChildrenElementsByTagName(element, Constants.RIGHT).get(0);
		temp = XML.getChildrenElements(temp).get(0);
		right = (Term) JavaClassesFactory.getTerm(temp);
	}

	@Override
	public String toString() {
		return left + " => " + right;
	}
	
	@Override
	public String toMaude() {
		String left = this.left == null ? "null" : this.left.toMaude();
		String right = this.right == null ? "null" : this.right.toMaude();
		
		return "_=>_(" + left + "," + right + ")";
	}
}

package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;

public class Configuration extends Sentence {

	public Configuration(Element element) {
		super(element);
		this.body = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public String toString() {
		String content = "  configuration ";
		content += this.body + " ";
		return content;
	}
}

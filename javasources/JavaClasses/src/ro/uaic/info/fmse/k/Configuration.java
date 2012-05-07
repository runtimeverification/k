package ro.uaic.info.fmse.k;

import java.util.HashMap;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class Configuration extends Sentence {

	public Configuration(Element element) {
		super(element);
		this.body = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(
				element).get(0));
		this.attributes = new HashMap<String, String>();
	}

	public String toString() {
		String content = "  configuration ";
		content += this.body + " ";
		return content;
	}

	@Override
	public String toMaude() {
		return "mb configuration " + super.toMaude();
	}

	@Override
	public Element toXml(Document doc) {
		Element configuration = doc.createElement(Constants.CONFIG);
		configuration.setTextContent("notimplementedyet");
		return configuration;

	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		body.accept(visitor);
	}
}

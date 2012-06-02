package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Import extends ModuleItem {

	String name;

	public Import(Element element) {
		super(element);
		name = element.getAttribute(Constants.NAME_name_ATTR);
	}

	public Import(String importName) {
		super((Element)null);
		name = importName;
	}

	@Override
	public String toString() {
		return "  imports " + name;
	}

	@Override
	public String toMaude() {
		return "including " + name + " .";
	}

	@Override
	public Element toXml(Document doc) {
		Element import_ = doc.createElement(Constants.IMPORT);
		import_.setTextContent(name);
		return import_;
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
	@Override
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
}

package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Configuration extends Sentence {

	public Configuration() {
		super("File System", "generated");
	}
	
	public Configuration(String location, String filename) {
		super(location, filename);
	}

	public Configuration(Element element) {
		super(element);
	}

	public Configuration(Configuration node) {
		super(node);
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
	}

	@Override
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
	
	@Override
	public Configuration shallowCopy() {
		return new Configuration(this);
	}
}

package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

/**
 * Used as a container for unparsed sentences like rule, context and configuration.
 * 
 * @author Radu
 * 
 */
public class StringSentence extends ModuleItem {
	private String content;

	public StringSentence(Element element) {
		super(element);
		content = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public StringSentence(StringSentence node) {
		super(node);
		this.content = node.content;
	}

	public String toString() {
		return "String sentence.";
	}

	@Override
	public String toMaude() {

		return "StringSentence should not be maudifiable.";
	}

	@Override
	public Element toXml(Document doc) {
		Element rule = doc.createElement(Constants.RULE);
		rule.setTextContent("notImplementedYet");
		return rule;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	public String getContent() {
		return content;
	}

	public void setContent(String content) {
		this.content = content;
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public StringSentence shallowCopy() {
		return new StringSentence(this);
	}
}

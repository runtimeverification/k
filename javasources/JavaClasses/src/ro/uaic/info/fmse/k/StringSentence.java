package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

/**
 * Used as a container for unparsed sentences like rule, context and configuration.
 * 
 * @author Radu
 * 
 */
public class StringSentence extends Sentence {
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
		String content = "  rule ";

		if (this.content != null && !this.content.equals(""))
			content += "[" + this.content + "]: ";

		content += this.body + " ";

		return content + attributes;
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
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}

	public String getContent() {
		return content;
	}

	public void setContent(String content) {
		this.content = content;
	}
}

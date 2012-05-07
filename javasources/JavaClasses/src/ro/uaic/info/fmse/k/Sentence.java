package ro.uaic.info.fmse.k;

import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Visitor;

public abstract class Sentence extends ModuleItem {
	public Sentence(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	Term body;
	Term condition = null;
	Map<String, String> attributes;

	@Override
	public String toMaude() {
		if (body != null)
			return body.toMaude() + " : KSentence [metadata \"" + getMetadata()
					+ "\"] .";
		return " : KSentence [metadata \"" + getMetadata() + "\"] .";
	}

	public String getMetadata() {
		java.util.List<String> reject = new LinkedList<String>();
		reject.add("cons");
		reject.add("klabel");
		reject.add("latex");

		String attributes = "";
		for (Entry<String, String> entry : this.attributes.entrySet()) {
			if (!reject.contains(entry.getKey()))
				attributes += " " + entry.getKey() + "=(" + entry.getValue()
						+ ")";
		}

		// append locations too
		attributes += " location=" + getMaudeLocation();

		return attributes.trim();
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		body.accept(visitor);
		if (condition != null)
			condition.accept(visitor);
	}
}

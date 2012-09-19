package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.utils.utils.xml.XML;
import org.w3c.dom.Element;


public abstract class Sentence extends ModuleItem {
	Term body;
	Term condition = null;
	Attributes attributes;

	public Sentence(Sentence s) {
		super(s);
		this.body = s.body;
		this.condition = s.condition;
		this.attributes = s.attributes;
	}

	public Sentence() {
		super();
		attributes = new Attributes();
	}

	public Sentence(String location, String filename) {
		super(location, filename);
		attributes = new Attributes();
	}

	public Sentence(Element element) {
		super(element);

		Element elm = XML.getChildrenElementsByTagName(element, Constants.BODY).get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.body = (Term) JavaClassesFactory.getTerm(elmBody);

		java.util.List<Element> its = XML.getChildrenElementsByTagName(element, Constants.COND);
		if (its.size() > 0)
			this.condition = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(its.get(0)).get(0));

		its = XML.getChildrenElementsByTagName(element, Constants.ATTRIBUTES);
		// assumption: <attributes> appears only once
		if (its.size() > 0) {
			attributes = (Attributes) JavaClassesFactory.getTerm(its.get(0));
		} else
			attributes = new Attributes("generated", "generated");
	}

	@Override
	public String toMaude() {

		String cond = "";
		if (condition != null)
			cond = "when " + condition.toMaude();

		return body.toMaude() + " " + cond + " : KSentence [metadata \"" + attributes.toMaude() + " location=" + getMaudeLocation() + "\"] .";
	}

	public Term getBody() {
		return body;
	}

	public void setBody(Term body) {
		this.body = body;
	}

	public Term getCondition() {
		return condition;
	}

	public void setCondition(Term condition) {
		this.condition = condition;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		this.body = (Term) visitor.modify(body);
		if (this.condition != null)
			this.condition = (Term) visitor.modify(condition);
	}

	public Attributes getAttributes() {
		return attributes;
	}

	public void setAttributes(Attributes attributes) {
		this.attributes = attributes;
	}
	
	@Override
	public abstract Sentence shallowCopy();
}

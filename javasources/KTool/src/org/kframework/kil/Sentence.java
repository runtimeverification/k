package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/**
 * A rule, configuration declaration, or context.
 * Each parses as a term, this class declares common members
 * {@link #body} and {@link #condition}, which have different
 * interpretations in the subclasses.
 */
public abstract class Sentence extends ModuleItem {
	Term body;
	Term condition = null;

	public Sentence(Sentence s) {
		super(s);
		this.body = s.body;
		this.condition = s.condition;
	}

	public Sentence() {
		super();
		attributes = new Attributes();
	}

	public Sentence(String location, String filename) {
		super(location, filename);
		if (attributes == null)
			attributes = new Attributes();
	}

	public Sentence(ATermAppl element) {
		super(element);
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
		// assumption: <cellAttributes> appears only once
		if (its.size() > 0) {
			attributes.setAll((Attributes) JavaClassesFactory.getTerm(its.get(0)));
		} else {
			if (attributes == null)
				attributes = new Attributes();
			attributes.addAttribute("generated", "generated");
		}
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
	public abstract Sentence shallowCopy();
}

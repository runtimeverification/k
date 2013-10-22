package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/**
 * A rule, configuration declaration, or context.
 * Each parses as a term, this class declares common members
 * {@link #body} and {@link #requires}, which have different
 * interpretations in the subclasses.
 */
public class Sentence extends ModuleItem {
	/** Label from {@code rule[}label{@code ]:} syntax or "". Currently unrelated to attributes */
	String label = "";
	Term body;
	Term requires = null;
	Term ensures = null;

	public Sentence(Sentence s) {
		super(s);
		this.body = s.body;
		this.label = s.label;
		this.requires = s.requires;
		this.ensures = s.ensures;
	}

	public Sentence() {
		super();
		attributes = new Attributes();
	}

	public Sentence(ATermAppl atm) {
		setLocation(atm);

		if (atm.getName().equals("Ensures")) {
			ensures = (Term) JavaClassesFactory.getTerm(atm.getArgument(1));
		}
		atm = (ATermAppl) atm.getArgument(0);

		body = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));

		if (atm.getName().equals("RequiresSentence")) {
			requires = (Term) JavaClassesFactory.getTerm(atm.getArgument(1));
		}
	}

	public Sentence(Element element) {
		setLocation(element);

		label = element.getAttribute(Constants.LABEL);
		Element elm = XML.getChildrenElementsByTagName(element, Constants.BODY).get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.body = (Term) JavaClassesFactory.getTerm(elmBody);

		java.util.List<Element> its = XML.getChildrenElementsByTagName(element, Constants.COND);
		if (its.size() > 0)
			this.requires = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(its.get(0)).get(0));

		its = XML.getChildrenElementsByTagName(element, "ensures");
		if (its.size() > 0)
			this.ensures = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(its.get(0)).get(0));

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

	public Term getRequires() {
		return requires;
	}

	public void setRequires(Term requires) {
		this.requires = requires;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public Sentence shallowCopy() {
		return new Sentence(this);
	}

	public String getLabel() {
		return label;
	}

	public void setLabel(String label) {
		this.label = label;
	}

	public String toString() {
		String content = "";

		if (this.label != null && !this.label.equals(""))
			content += "[" + this.label + "]: ";

		content += this.body + " ";
		if (this.requires != null) {
			content += "requires " + this.requires + " ";
		}
		if (this.ensures != null) {
			content += "ensures " + this.ensures + " ";
		}

		return content + attributes;
	}

	public Term getEnsures() {
		return ensures;
	}

	public void setEnsures(Term ensures) {
		this.ensures = ensures;
	}
}

package org.kframework.kil;

import java.util.ArrayList;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.utils.xml.XML;

public class PriorityBlock extends ASTNode {

	java.util.List<Production> productions = new ArrayList<Production>();
	String assoc;

	public java.util.List<Production> getProductions() {
		return productions;
	}

	public void setProductions(java.util.List<Production> productions) {
		this.productions = productions;
	}

	public String getAssoc() {
		return assoc;
	}

	public void setAssoc(String assoc) {
		this.assoc = assoc;
	}

	public PriorityBlock() {
		super();
		this.assoc = "";
	}

	public PriorityBlock(Element element) {
		super(element);

		java.util.List<Element> productions = XML.getChildrenElementsByTagName(element, Constants.PRODUCTION);
		for (Element production : productions)
			this.productions.add((Production) JavaClassesFactory.getTerm(production));

		assoc = element.getAttribute(Constants.ASSOC_assoc_ATTR);
	}

	public PriorityBlock(PriorityBlock node) {
		super(node);
		this.assoc = node.assoc;
		this.productions.addAll(node.productions);
	}

	@Override
	public String toString() {
		String content = "";
		for (Production production : productions)
			content += production + "\n| ";

		if (content.length() > 2)
			content = content.substring(0, content.length() - 3);

		if (assoc.equals(""))
			return content;
		return assoc + ": " + content;
	}

	@Override
	public String toMaude() {
		return "production";
	}

	@Override
	public void applyToAll(Modifier visitor) {
		for (int i = 0; i < this.productions.size(); i++) {
			Production elem = (Production) visitor.modify(this.productions.get(i));
			this.productions.set(i, elem);
		}
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (this == obj)
			return true;
		if (!(obj instanceof PriorityBlock))
			return false;
		PriorityBlock pb = (PriorityBlock) obj;

		if (!pb.getAssoc().equals(this.assoc))
			return false;

		if (pb.productions.size() != productions.size())
			return false;

		for (int i = 0; i < pb.productions.size(); i++) {
			if (!pb.productions.get(i).equals(productions.get(i)))
				return false;
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = assoc.hashCode();

		for (Production prd : productions)
			hash += prd.hashCode();
		return hash;
	}

	@Override
	public PriorityBlock shallowCopy() {
		return new PriorityBlock(this);
	}
}

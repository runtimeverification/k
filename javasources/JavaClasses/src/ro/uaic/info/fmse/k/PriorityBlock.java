package ro.uaic.info.fmse.k;

import java.util.LinkedList;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class PriorityBlock extends ASTNode {

	java.util.List<Production> productions;
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

	public PriorityBlock(Element element) {
		super(element);

		this.productions = new LinkedList<Production>();
		java.util.List<Element> productions = XML.getChildrenElementsByTagName(element, Constants.PRODUCTION);
		for (Element production : productions)
			this.productions.add((Production) JavaClassesFactory.getTerm(production));

		assoc = element.getAttribute(Constants.ASSOC_assoc_ATTR);
	}

	public PriorityBlock(PriorityBlock node) {
		super(node);
		this.assoc = node.assoc;
		this.productions = node.productions;
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
	public Element toXml(Document doc) {
		Element priority = doc.createElement(Constants.PRIORITY);

		for (Production p : productions)
			priority.appendChild(p.toXml(doc));

		return priority;
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
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
}

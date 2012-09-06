package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class KApp extends Term {
	Term label;
	Term child;

	public KApp(String location, String filename) {
		super(location, filename, "K");
	}

	public KApp(String location, String filename, Term label, Term child) {
		super(location, filename, "K");
		this.label = label;
		this.child = child;
	}

	public KApp(Term label, Term child) {
		super("K");
		this.label = label;
		this.child = child;
	}
	
	public KApp(Element element) {
		super(element);
		Element elm = XML.getChildrenElements(element).get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.label = (Term) JavaClassesFactory.getTerm(elmBody);

		elm = XML.getChildrenElements(element).get(1);
		this.child = (Term) JavaClassesFactory.getTerm(elm);
	}

	public KApp(KApp node) {
		super(node);
		this.label = node.label;
		this.child = node.child;
	}

	public String toString() {
		return this.label + "(" + this.child + ")";
	}

	@Override
	public String toMaude() {
		return "_`(_`)(" + label.toMaude() + ", " + child.toMaude() + ") ";
	}

	public Term getLabel() {
		return label;
	}

	public void setLabel(Term label) {
		this.label = label;
	}

	public Term getChild() {
		return child;
	}

	public void setChild(Term child) {
		this.child = child;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		this.label = (Term) visitor.modify(label);
		this.child = (Term) visitor.modify(child);
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
	public KApp shallowCopy() {
		return new KApp(this);
	}
}

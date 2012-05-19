package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Modifier;
import ro.uaic.info.fmse.parsing.Transformer;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class Rewrite extends Term {
	private Term left;
	private Term right;

	public Rewrite(Element element) {
		super(element);

		Element temp = XML.getChildrenElementsByTagName(element, Constants.LEFT).get(0);
		temp = XML.getChildrenElements(temp).get(0);
		left = (Term) JavaClassesFactory.getTerm(temp);
		temp = XML.getChildrenElementsByTagName(element, Constants.RIGHT).get(0);
		temp = XML.getChildrenElements(temp).get(0);
		right = (Term) JavaClassesFactory.getTerm(temp);
	}

	public Rewrite(Rewrite node) {
		super(node);
		this.left = node.left;
		this.right = node.right;
	}

	public void setLeft(Term left) {
		this.left = left;
	}

	public Term getLeft() {
		return left;
	}

	public void setRight(Term right) {
		this.right = right;
	}

	public Term getRight() {
		return right;
	}

	@Override
	public String toString() {
		return left + " => " + right;
	}

	@Override
	public String toMaude() {
		String left = this.left == null ? "null" : this.left.toMaude();
		String right = this.right == null ? "null" : this.right.toMaude();

		return "_=>_(" + left + "," + right + ")";
	}

	@Override
	public void applyToAll(Modifier visitor) {
		left = (Term) visitor.modify(left);
		right = (Term) visitor.modify(right);
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

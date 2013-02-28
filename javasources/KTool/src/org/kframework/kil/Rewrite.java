package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/**
 * Represents {@code =>} in the syntax of rules.
 * May occur in multiple places in the body of a {@link Rule}, but
 * may not be nested.
 */
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

	public Rewrite(Term eval1Left, Term eval1Right) {
		super(eval1Left.getSort());
		left = eval1Left;
		right = eval1Right;
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
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

  @Override
  public void accept(Matcher matcher, Term toMatch){
    matcher.match(this, toMatch);
  }

	// public String getComputedSort() {
	// if (sort.equals(MetaK.Constants.KList)) {
	// String lsort = left.getSort();
	// String rsort = right.getSort();
	//
	// if (!lsort.equals(MetaK.Constants.KList) && !rsort.equals(MetaK.Constants.KList))
	// sort = "K";
	// }
	// return sort;
	// }

	@Override
	public Rewrite shallowCopy() {
		return new Rewrite(this);
	}

  //this currently causes ambiguities
/*	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Rewrite)) return false;
		Rewrite r = (Rewrite)o;
		return left.equals(r.left) && right.equals(r.right);
	} */
}

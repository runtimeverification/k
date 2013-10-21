package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

import com.google.common.collect.ImmutableSet;

/**
 * Represents {@code =>} in the syntax of rules. May occur in multiple places in the body of a {@link Rule}, but may not be nested.
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

	public Rewrite(ATermAppl atm) {
		super(atm);
		this.sort = StringUtil.getSortNameFromCons(atm.getName());

		left = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));
		right = (Term) JavaClassesFactory.getTerm(atm.getArgument(1));
	}

	public Rewrite(Rewrite node) {
		super(node);
		this.left = node.left;
		this.right = node.right;
	}

	public Rewrite(Term eval1Left, Term eval1Right, Context context) {
		super(eval1Left.getSort());
		left = eval1Left;
		right = eval1Right;
		recomputeSort(context);
	}

	/**
	 * Returning the Least Upper Bound for left and right sorts, unless either side is an ambiguity, in which case arbitrary return the left sort.
	 */
	private void recomputeSort(Context context) {
		if (left instanceof Ambiguity || right instanceof Ambiguity)
			super.getSort();
		else
			sort = context.getLUBSort(ImmutableSet.of(left.getSort(), right.getSort()));
	}

	public Term getLeft() {
		return left;
	}

	public Term getRight() {
		return right;
	}

	public void replaceChildren(Term left, Term right, Context context) {
		this.left = left;
		this.right = right;
		recomputeSort(context);
	}

	public void setLeft(Term left, Context context) {
		this.left = left;
		recomputeSort(context);
	}

	public void setRight(Term right, org.kframework.kil.loader.Context context) {
		this.right = right;
		recomputeSort(context);
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
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public void accept(Matcher matcher, Term toMatch) {
		matcher.match(this, toMatch);
	}

	@Override
	public Rewrite shallowCopy() {
		return new Rewrite(this);
	}

	@Override
	public int hashCode() {
		return 59 * left.hashCode() + right.hashCode();
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Rewrite))
			return false;
		Rewrite r = (Rewrite) o;
		return left.equals(r.left) && right.equals(r.right);
	}

	@Override
	public boolean contains(Object o) {
		if (o instanceof Bracket)
			return contains(((Bracket) o).getContent());
		if (o instanceof Cast)
			return contains(((Cast) o).getContent());
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Rewrite))
			return false;
		Rewrite r = (Rewrite) o;
		return left.contains(r.left) && right.contains(r.right);
	}
}

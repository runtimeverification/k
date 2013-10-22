package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/**
 * Variables, used both in rules/contexts and for variables like {@code $PGM} in configurations.
 */
public class Variable extends Term {

	private static int nextVariableIndex = 0;

	private String name;
	/** True if the variable was written with an explicit type annotation */
	private boolean userTyped = false;
	private boolean fresh = false;
	private boolean syntactic = false;
	/** Used by the type inferencer  */
	private String expectedSort = null;

	public String getExpectedSort() {
		return expectedSort;
	}

	public void setExpectedSort(String expectedSort) {
		this.expectedSort = expectedSort;
	}

	public Variable(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.name = element.getAttribute(Constants.NAME_name_ATTR);
		this.userTyped = element.getAttribute(Constants.TYPE_userTyped_ATTR).equals("true");
		if (this.name.startsWith("?")) {
			this.setFresh(true);
			this.name = this.name.substring(1);
		}
	}

	public Variable(ATermAppl atm) {
		super(atm);
		this.sort = StringUtil.getSortNameFromCons(atm.getName());

		name = ((ATermAppl) atm.getArgument(0)).getName();

		if (atm.getName().endsWith("2Var"))
			this.userTyped = true;
		if (this.name.startsWith("?")) {
			this.setFresh(true);
			this.name = this.name.substring(1);
		}
	}

	public Variable(String name, String sort) {
		super(sort);
		this.name = name;
	}

	public Variable(Variable variable) {
		super(variable);
		name = variable.name;
		fresh = variable.fresh;
		userTyped = variable.userTyped;
		syntactic = variable.syntactic;
        expectedSort = variable.expectedSort;
	}

	public static Variable getFreshVar(String sort) {
		return new Variable("GeneratedFreshVar" + nextVariableIndex++, sort);
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public String toString() {
		return name + ":" + sort + " ";
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
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (this == obj)
			return true;
		if (!(obj instanceof Variable))
			return false;
		Variable var = (Variable) obj;

		return this.sort.equals(var.getSort()) && this.name.equals(var.getName());
	}

	@Override
	public int hashCode() {
		return sort.hashCode() + name.hashCode();
	}

	public void setUserTyped(boolean userTyped) {
		this.userTyped = userTyped;
	}

	public boolean isUserTyped() {
		return userTyped;
	}

	@Override
	public Variable shallowCopy() {
		return new Variable(this);
	}

	public void setFresh(boolean fresh) {
		this.fresh = fresh;
	}

	public boolean isFresh() {
		return fresh;
	}

	public boolean isSyntactic() {
		return syntactic;
	}

	public void setSyntactic(boolean syntactic) {
		this.syntactic = syntactic;
	}
}

package org.kframework.kil;

import java.util.List;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/**
 *
 */
public class Restrictions extends ModuleItem {
	Sort sort;
	Terminal terminal;
	String pattern;

	public Sort getSort() {
		return sort;
	}

	public void setSort(Sort sort) {
		this.sort = sort;
	}

	public Restrictions(Element element) {
		super(element);

		List<Element> sorts = XML.getChildrenElementsByTagName(element, Constants.SORT);
		// assumption: sorts contains only one element
		if (sorts.size() > 0)
			sort = (Sort) JavaClassesFactory.getTerm(sorts.get(0));
		else {
			List<Element> terminals = XML.getChildrenElementsByTagName(element, Constants.TERMINAL);
			terminal = (Terminal) JavaClassesFactory.getTerm(terminals.get(0));
		}

		this.pattern = StringUtil.unescape(element.getAttribute(Constants.VALUE_value_ATTR));
	}

	public Restrictions(String sort, String terminal, String pattern) {
		if (sort != null && terminal != null)
			System.out.println("A restriction can have only one of sort or terminal!");
		if (sort != null)
			this.sort = new Sort(sort);
		else
			this.terminal = new Terminal(terminal);
		this.pattern = pattern;
	}

	public Restrictions(Restrictions node) {
		super(node);
		this.sort = node.sort;
		this.terminal = node.terminal;
		this.pattern = node.pattern;
	}

	@Override
	public String toString() {
		return "  syntax " + (sort != null ? sort : terminal) + " -/- " + pattern + "\n";
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
		if (!(obj instanceof Restrictions))
			return false;
		Restrictions syn = (Restrictions) obj;
		if (!pattern.equals(syn.pattern))
			return false;

		if (!(sort != null ? sort.equals(syn.sort) : terminal.equals(syn.terminal)))
			return false;
		return true;
	}

	@Override
	public int hashCode() {
		int hash = pattern.hashCode();
		hash += sort != null ? sort.hashCode() : terminal.hashCode();
		return hash;
	}

	@Override
	public Restrictions shallowCopy() {
		return new Restrictions(this);
	}

	public Terminal getTerminal() {
		return terminal;
	}

	public void setTerminal(Terminal terminal) {
		this.terminal = terminal;
	}

	public String getPattern() {
		return pattern;
	}

	public void setPattern(String pattern) {
		this.pattern = pattern;
	}
}

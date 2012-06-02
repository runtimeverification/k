package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Variable extends Term {
	private String name;

	public Variable(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.name = element.getAttribute(Constants.NAME_name_ATTR);
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
	public String toMaude() {
		if (name.equals("_"))
			return "?:" + sort;
		return name + ":" + sort;
	}

	public void accept(Modifier visitor) {
		visitor.modify(this);
	}

	@Override
	public void applyToAll(Modifier visitor) {
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
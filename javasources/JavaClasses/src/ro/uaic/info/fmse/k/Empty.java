package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.parsing.Modifier;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;

public class Empty extends Term {

	public Empty(String location, String filename) {
		super(location, filename);
	}

	public Empty(String location, String filename, String sort) {
		super(location, filename);
		this.sort = sort;
	}

	public Empty(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
	}

	public String toString() {
		return "." + sort + " ";
	}

	@Override
	public String toMaude() {
		if (MaudeHelper.basicSorts.contains(sort)) {
			if (!sort.equals("List{K}"))
				return "(.)." + sort;
			else
				return "." + sort;
		}
		// search for the separator for the empty list
		Production prd = DefinitionHelper.listConses.get(getSort());
		UserList ul = (UserList) prd.getItems().get(0);
		return ".List`{\"" + ul.separator + "\"`}";
	}

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}

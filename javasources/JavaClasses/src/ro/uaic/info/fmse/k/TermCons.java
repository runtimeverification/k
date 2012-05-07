package ro.uaic.info.fmse.k;

import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class TermCons extends Term {
	String sort;
	String cons;
	boolean builtin = false;
	protected java.util.List<Term> contents;

	public TermCons(Element element, boolean builtin) {
		super(element);
		this.builtin = builtin;
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.cons = element.getAttribute(Constants.CONS_cons_ATTR);

		contents = new LinkedList<Term>();
		List<Element> children = XML.getChildrenElements(element);
		for (Element e : children)
			contents.add((Term) JavaClassesFactory.getTerm(e));
	}

	public String toString() {
		String str = "";
		Production pr = DefinitionHelper.conses.get("\"" + cons + "\"");

		if (pr.items.size() > 0) {
			if (pr.items.get(0).getType() == ProductionType.USERLIST) {
				String separator = ((UserList) pr.items.get(0)).separator;
				str = contents.get(0) + " " + separator + " " + contents.get(1) + " ";
			} else
				for (int i = 0, j = 0; i < pr.items.size(); i++) {
					ProductionItem pi = pr.items.get(i);
					if (pi.getType() == ProductionType.TERMINAL) {
						String terminall = pi.toString();
						terminall = terminall.substring(1, terminall.length() - 1);
						str += terminall + " ";
					} else if (pi.getType() == ProductionType.SORT)
						str += contents.get(j++) + " ";
				}
		}
		return str;
	}

	@Override
	public String toMaude() {
		Production pr = DefinitionHelper.conses.get("\"" + cons + "\"");
		String cons = pr.getLabel();

		String contents = "";
		for (Term term : this.contents)
			if (term != null)
				contents += term.toMaude() + ",";
			else
				contents += term + ",";

		if (contents.length() >= 1)
			contents = "(" + contents.substring(0, contents.length() - 1) + ")";

		return cons + contents;
	}

	public void accept(Visitor visitor) {
		visitor.visit(this);
		for (ASTNode di : contents)
			di.accept(visitor);
	}

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	public String getCons() {
		return cons;
	}

	public void setCons(String cons) {
		this.cons = cons;
	}

	public boolean isBuiltin() {
		return builtin;
	}

	public void setBuiltin(boolean builtin) {
		this.builtin = builtin;
	}

	public java.util.List<Term> getContents() {
		return contents;
	}

	public void setContents(java.util.List<Term> contents) {
		this.contents = contents;
	}
}

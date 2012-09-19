package org.kframework.k;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ProductionItem.ProductionType;
import org.kframework.loader.Constants;
import org.kframework.loader.DefinitionHelper;
import org.kframework.loader.JavaClassesFactory;
import org.kframework.visitors.Modifier;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.utils.xml.XML;

public class TermCons extends Term {
	String cons;
	protected java.util.List<Term> contents;

	public TermCons(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.cons = element.getAttribute(Constants.CONS_cons_ATTR);

		contents = new LinkedList<Term>();
		List<Element> children = XML.getChildrenElements(element);
		for (Element e : children)
			contents.add((Term) JavaClassesFactory.getTerm(e));
	}

	public TermCons(String sort, String cons) {
		super(sort);
		this.cons = cons;
		contents = new ArrayList<Term>();
	}
	
	public TermCons(String location, String filename, String sort, String listCons, List<Term> genContents) {
		super(location, filename, sort);
		cons = listCons;
		contents = genContents;
	}

	public TermCons(TermCons node) {
		super(node);
		this.cons = node.cons;
		this.contents = node.contents;
	}

	public Production getProduction() {
		return DefinitionHelper.conses.get(getCons());
	}

	public String toString() {
		String str = "";
		Production pr = DefinitionHelper.conses.get(cons);

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
		Production pr = DefinitionHelper.conses.get(cons);
		String cons = pr.getLabel();

		if (pr.attributes.containsKey("maudeop"))
			cons = pr.attributes.get("maudeop").replaceAll("\"", "");

		String contents = "";
		for (Term term : this.contents)
			if (term != null)
				contents += term.toMaude() + ",";
			else
				contents += term + ",";

		if (contents.length() >= 1)
			contents = "(" + contents.substring(0, contents.length() - 1) + ")";
			
		cons = cons.replaceAll(" ", "`");
		return cons + contents;
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

	public java.util.List<Term> getContents() {
		return contents;
	}

	public void setContents(java.util.List<Term> contents) {
		this.contents = contents;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		for (int i = 0; i < this.contents.size(); i++) {
			Term elem = (Term) visitor.modify(this.contents.get(i));
			this.contents.set(i, elem);
		}
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
		if (!(obj instanceof TermCons))
			return false;
		TermCons tc = (TermCons) obj;

		if (!tc.getSort().equals(this.sort))
			return false;
		if (!tc.cons.equals(cons))
			return false;

		if (tc.contents.size() != contents.size())
			return false;

		for (int i = 0; i < tc.contents.size(); i++) {
			if (!tc.contents.get(i).equals(contents.get(i)))
				return false;
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = sort.hashCode() + cons.hashCode();

		for (Term t : contents)
			hash += t.hashCode();
		return hash;
	}

	@Override
	public TermCons shallowCopy() {
		return new TermCons(this);
	}
}

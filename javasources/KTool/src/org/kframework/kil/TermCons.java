package org.kframework.kil;

import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.List;

public class TermCons extends Term {
	protected final String cons;
	protected java.util.List<Term> contents;

	public TermCons(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.cons = element.getAttribute(Constants.CONS_cons_ATTR);

		contents = new ArrayList<Term>();
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

	public TermCons(String psort, String listCons, List<Term> genContents) {
		super(psort);
		cons = listCons;
		contents = genContents;
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

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	public String getCons() {
		return cons;
	}

	public java.util.List<Term> getContents() {
		return contents;
	}

	public void setContents(java.util.List<Term> contents) {
		this.contents = contents;
	}

    public Term getSubterm(int idx) {
        return contents.get(idx);
    }

    public Term setSubterm(int idx, Term term) {
        return contents.set(idx, term);
    }

    public int arity() {
        return getProduction().getArity();
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

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.loader.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/**
 * Applications that are not in sort K, or have not yet been flattened.
 */
public class TermCons extends Term implements Interfaces.MutableList<Term, Enum<?>> {
    /** A unique identifier corresponding to a production, matching the SDF cons */
    protected final String cons;
    protected java.util.List<Term> contents;
    protected Production production;

    private int cachedHashCode = 0;
    private boolean upToDateHash = false;

    public TermCons(Element element, Context context) {
        super(element);
        this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
        this.cons = element.getAttribute(Constants.CONS_cons_ATTR);
        this.production = context.conses.get(cons);
        assert this.production != null;

        contents = new ArrayList<Term>();
        List<Element> children = XML.getChildrenElements(element);
        for (Element e : children)
            contents.add((Term) JavaClassesFactory.getTerm(e));
    }

    public TermCons(String sort, String cons, org.kframework.kil.loader.Context context) {
        this(sort, cons, new ArrayList<Term>(), context);
    }

    public TermCons(TermCons node) {
        super(node);
        this.cons = node.cons;
        this.contents = new ArrayList<Term>(node.contents);
        this.production = node.production;
        assert this.production != null;
    }

    public TermCons(String psort, String listCons, List<Term> genContents, Context context) {
        super(psort);
        cons = listCons;
        contents = genContents;
        production = context.conses.get(cons);
    }

    public TermCons(String psort, List<Term> contents, Production production) {
        super(psort);
        cons = null;
        this.contents = contents;
        this.production = production;
    }

    public Production getProduction() {
        return production;
    }

    @Override
    public String toString() {
        String str = "";
        if (production.items.size() > 0) {
            if (production.isListDecl()) {
                String separator = ((UserList) production.items.get(0)).separator;
                if (contents.size() == 0)
                    str += "." + sort;
                else {
                    str += "'_" + separator + "_(";
                    for (Term t : contents)
                        str += t + ", ";
                    str = str.substring(0, str.length()-2) + ")";
                }
            } else
                for (int i = 0, j = 0; i < production.items.size(); i++) {
                    ProductionItem pi = production.items.get(i);
                    if (pi instanceof Terminal) {
                        str += ((Terminal) pi).getTerminal() + " ";
                    } else if (pi instanceof Sort)
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
        upToDateHash = false;
        return contents;
    }

    public void setContents(java.util.List<Term> contents) {
        this.contents = contents;
        upToDateHash = false;
    }

    public Term getSubterm(int idx) {
        return contents.get(idx);
    }

    public Term setSubterm(int idx, Term term) {
        return contents.set(idx, term);
    }

    public int arity() {
        return production.getArity();
    }

    public boolean isListTerminator() {
        return production.isListDecl() && contents.size() == 0;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        TermCons tc = (TermCons) obj;

        if (!tc.getSort().equals(sort))
            return false;
        if (cons != null ? !cons.equals(tc.cons) : tc.cons != null) return false;
        if (!production.equals(tc.production)) return false;
        if (contents.size() != tc.contents.size()) return false;
        for (int i = 0; i < tc.contents.size(); i++) {
            if (!tc.contents.get(i).equals(contents.get(i)))
                return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        if (!upToDateHash) {
            cachedHashCode = cons != null ? cons.hashCode() : 0;
            cachedHashCode = 31 * cachedHashCode + production.hashCode();
            for (Term t : contents)
                cachedHashCode = 31 * cachedHashCode + t.hashCode();
            upToDateHash = true;
        }
        return cachedHashCode;
    }

    @Override
    public boolean contains(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (obj instanceof Bracket)
            return contains(((Bracket) obj).getContent());
        if (obj instanceof Cast)
            return contains(((Cast) obj).getContent());
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
            if (!contents.get(i).contains(tc.contents.get(i)))
                return false;
        }

        return true;
    }

    @Override
    public TermCons shallowCopy() {
        return new TermCons(this);
    }

    @Override
    public List<Term> getChildren(Enum<?> type) {
        return contents;
    }

    @Override
    public void setChildren(List<Term> children, Enum<?> cls) {
        this.contents = children;
    }
}

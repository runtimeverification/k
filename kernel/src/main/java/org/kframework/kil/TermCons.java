// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/**
 * Applications that are not in sort K, or have not yet been flattened.
 */
public class TermCons extends ProductionReference implements Interfaces.MutableList<Term, Enum<?>> {
    protected java.util.List<Term> contents;

    /**
     * Since TermCons refers to a production instance rather than a unique identifier,
     * replacing a production with a different production in the definition is not
     * intrinsically safe.
     *
     * TODO(dwightguth): make TermCons used only in the parser where productions should not
     * change.
     */

    private int cachedHashCode = 0;
    private boolean upToDateHash = false;

    public TermCons(Element element, JavaClassesFactory factory, Map<String, Production> conses){
        super(element, conses);
        this.sort = Sort.of(element.getAttribute(Constants.SORT_sort_ATTR));
        assert this.production != null;

        contents = new ArrayList<Term>();
        List<Element> children = XML.getChildrenElements(element);
        for (Element e : children)
            contents.add((Term) factory.getTerm(e));
    }

    public TermCons(Sort sort, Production p) {
        this(sort, new ArrayList<Term>(), p);
    }

    public TermCons(TermCons node) {
        super(node);
        this.contents = new ArrayList<Term>(node.contents);
        assert this.production != null;
    }

    public TermCons(Sort psort, List<Term> contents, Production production) {
        super(psort, production);
        this.contents = contents;
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
                    } else if (pi instanceof NonTerminal)
                        str += contents.get(j++) + " ";
                }
        }
        return str;
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
            cachedHashCode = production.hashCode();
            for (Term t : contents)
                cachedHashCode = 31 * cachedHashCode + t.hashCode();
            upToDateHash = true;
        }
        return cachedHashCode;
    }

    /**
     * TODO: (Radu) Make TermCons immutable
     * At the moment TermCons is mutable, so I am hacking it this way to invalidate the cache
     * but I will have to implement it correctly and make TermCons immutable.
     */
    public void invalidateHashCode() {
        upToDateHash = false;
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

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/** Base class for collection sorts */
public abstract class Collection extends Term implements Interfaces.MutableList<Term, Enum<?>> {

    protected java.util.List<Term> contents;

    public Collection(String sort) {
        super(sort);
        contents = new ArrayList<Term>();
    }

    public Collection(Collection c) {
        super(c);
        this.contents = new ArrayList<Term>(c.contents);
    }

    public Collection(String location, String filename, String sort) {
        super(location, filename, sort);
        contents = new ArrayList<Term>();
    }

    public Collection(Element element) {
        super(element);

        contents = new ArrayList<Term>();
        List<Element> children = XML.getChildrenElements(element);
        for (Element e : children)
            contents.add((Term) JavaClassesFactory.getTerm(e));
    }

    public Collection(String sort, List<Term> col) {
        super(sort);
        this.contents = col;
    }

    @Override
    public String toString() {
        String content = "";
        for (Term t : contents)
            content += t;
        if (content.equals("")) return "." + sort;
        return content;
    }

    public java.util.List<Term> getContents() {
        return contents;
    }

    public void setContents(java.util.List<Term> contents) {
        this.contents = contents;
    }

    public void add(Term t) {
        contents.add(t);
    }

    public boolean isEmpty() {
        return contents.isEmpty();
    }

    @Override
    public abstract Collection shallowCopy();

    @Override
    public boolean equals(Object o) {
        if (getClass() != o.getClass())
            return false;
        Collection c = (Collection) o;
        return sort.equals(c.sort) && contents.equals(c.contents);
    }

    @Override
    public boolean contains(Object o) {
        if (o instanceof Bracket)
            return contains(((Bracket) o).getContent());
        if (o instanceof Cast)
            return contains(((Cast) o).getContent());
        if (getClass() != o.getClass())
            return false;
        Collection c = (Collection) o;
        for (int i = 0; i < contents.size(); i++) {
            if (!contents.get(i).contains(c.contents.get(i))) {
                return false;
            }
        }
        return sort.equals(c.sort);
    }

    @Override
    public int hashCode() {
        return sort.hashCode() * 13 + contents.hashCode();
    }

    @Override
    public List<Term> getChildren(Enum<?> _) {
        return contents;
    }

    @Override
    public void setChildren(List<Term> children, Enum<?> _) {
        this.contents = children;
    }
}

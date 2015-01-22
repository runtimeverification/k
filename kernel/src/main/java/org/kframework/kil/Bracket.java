// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/** Represents parentheses uses for grouping. All productions labeled bracket parse to this. */
public class Bracket extends Term implements Interfaces.MutableParent<Term, Enum<?>> {

    private Term content;

    public Term getContent() {
        return content;
    }

    public void setContent(Term content) {
        this.content = content;
    }

    public Sort getSort() {
        if (content instanceof Ambiguity)
            return super.getSort();
        return content.getSort();
    }

    public Bracket(Bracket i) {
        super(i);
        this.content = i.content;
    }

    public Bracket(Term t, Context context) {
        super(t.getSort());
        this.content = t;
    }

    public Bracket(Location location, Source source, Sort sort) {
        super(location, source, sort);
    }

    public Bracket(Location location, Source source, Term t, Context context) {
        super(location, source, t.getSort());
        this.content = t;
    }

    public Bracket(Element element, JavaClassesFactory factory) {
        super(element);
        this.content = (Term) factory.getTerm(XML.getChildrenElements(element).get(0));
    }

    public Bracket(Sort sort) {
        super(sort);
    }

    @Override
    public Bracket shallowCopy() {
        return new Bracket(this);
    }

    @Override
    public String toString() {
        return "(" + content + ")";
    }

    @Override
    public int hashCode() {
        return content.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null)
            return false;
        if (this == o)
            return true;
        if (!(o instanceof Bracket))
            return false;
        Bracket b = (Bracket) o;
        return content.equals(b.content);
    }

    @Override
    public boolean contains(Object o) {
        if (o == null)
            return false;
        if (this == o)
            return true;
        if (!(o instanceof Bracket))
            return false;
        Bracket b = (Bracket) o;
        return content.contains(b.content);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Term getChild(Enum<?> type) {
        return content;
    }

    @Override
    public void setChild(Term child, Enum<?> type) {
        this.content = child;
    }
}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/** Represents parentheses uses for grouping. All productions labeled bracket parse to this. */
public class Cast extends Term implements Interfaces.MutableParent<Term, Enum<?>> {
    public enum CastType {
        /**
         * Casting of the form _:Sort. Sort restrictions are imposed for both the inner term, as well as the outer term.
         * This also creates a runtime check for the inner term.
         */
        SEMANTIC,
        /**
         * Casting of the form _::Sort. Sort restrictions are imposed for both the inner term, as well as the outer term.
         * No runtime checks.
         */
        SYNTACTIC,
        /**
         * Casting of the form _<:Sort. Sort restrictions are imposed only for the inner term.
         * The outer sort, namely the sort of this construct, is K. No runtime checks.
         */
        INNER,
        /**
         * Casting of the form _:>Sort. The sort of the inner production is restricted to K.
         * The outer sort, namely the sort of this construct, is Sort. No runtime checks.
         */
        OUTER
    }

    private Term content;
    private CastType type;

    public Term getContent() {
        return content;
    }

    public void setContent(Term content) {
        this.content = content;
    }

    public Cast(Cast i) {
        super(i);
        this.content = i.content;
        this.type = i.type;
    }

    public Cast(Term t, Context context) {
        super(t.getSort());
        this.content = t;
    }

    public Cast(Location location, Source source, Sort sort) {
        super(location, source, sort);
    }

    public Cast(Location location, Source source, Term t, org.kframework.kil.loader.Context context) {
        super(location, source, t.getSort());
        this.content = t;
    }

    public Cast(Element element) {
        super(element);
        if (element.getAttribute("type").equals("semantic"))
            this.type = CastType.SEMANTIC;
        else if (element.getAttribute("type").equals("syntactic"))
            this.type = CastType.SYNTACTIC;
        else if (element.getAttribute("type").equals("inner"))
            this.type = CastType.INNER;
        else if (element.getAttribute("type").equals("outer"))
            this.type = CastType.OUTER;
        this.content = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));

        java.util.List<Element> its = XML.getChildrenElementsByTagName(element, Constants.ATTRIBUTES);
        if (its.size() > 0) {
            getAttributes().putAll((Attributes) JavaClassesFactory.getTerm(its.get(0)));
        }
    }

    public Cast(Sort sort) {
        super(sort);
    }

    public Sort getSort() {
        if (type == CastType.INNER)
            return Sort.K;
        return sort;
    }

    public Sort getInnerSort() {
        if (type == CastType.OUTER)
            return Sort.K;
        return sort;
    }

    @Override
    public Cast shallowCopy() {
        return new Cast(this);
    }

    @Override
    public String toString() {
        return "(" + content + ")";
    }

    @Override
    public int hashCode() {
        return content.hashCode() + this.type.hashCode() + this.sort.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null)
            return false;
        if (this == o)
            return true;
        if (!(o instanceof Cast))
            return false;
        Cast c = (Cast) o;
        return this.type == c.type && this.content.equals(c.content);
    }

    @Override
    public boolean contains(Object o) {
        if (o == null)
            return false;
        if (this == o)
            return true;
        if (!(o instanceof Cast))
            return false;
        Cast c = (Cast) o;
        return this.type == c.type && this.content.contains(c.content);
    }

    public CastType getType() {
        return type;
    }

    public void setType(CastType type) {
        this.type = type;
    }

    public boolean isSyntactic() {
        return type != CastType.SEMANTIC;
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

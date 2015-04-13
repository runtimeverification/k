// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.w3c.dom.Element;

/** Subclasses wrap a term as an item in the corresponding collection */
public abstract class CollectionItem extends Term implements Interfaces.MutableParent<Term, CollectionItem.Children> {

    protected Term value;

    public static enum Children {
        KEY, VALUE
    }

    public CollectionItem(CollectionItem i) {
        super(i);
        this.value = i.value;
    }

    public CollectionItem(Location location, Source source, Sort sort) {
        super(location, source, sort);
    }

    public CollectionItem(Element element) {
        super(element);
    }

    public CollectionItem(Sort sort) {
        super(sort);
    }

    public void setItem(Term value) {
        this.value = value;
    }

    public Term getItem() {
        return value;
    }

    @Override
    public abstract CollectionItem shallowCopy();

    @Override
    public boolean equals(Object o) {
        if (getClass() != o.getClass())
            return false;
        CollectionItem c = (CollectionItem) o;
        return sort.equals(c.sort) && value.equals(c.value);
    }

    @Override
    public boolean contains(Object o) {
        if (o instanceof Bracket)
            return contains(((Bracket) o).getContent());
        if (o instanceof Cast)
            return contains(((Cast) o).getContent());
        if (getClass() != o.getClass())
            return false;
        CollectionItem c = (CollectionItem) o;
        return sort.equals(c.sort) && value.contains(c.value);
    }

    @Override
    public int hashCode() {
        return sort.hashCode() * 19 + value.hashCode();
    }

    @Override
    public Term getChild(Children type) {
        if (type == Children.VALUE) {
            return value;
        }
        throw new IllegalArgumentException("unexpected child type " + type.name());
    }

    @Override
    public void setChild(Term child, Children type) {
        if (type == Children.VALUE) {
            this.value = child;
        } else {
            throw new IllegalArgumentException("unexpected child type " + type.name());
        }
    }
}

// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

public class BagItem extends CollectionItem {
    public BagItem(Location location, Source source) {
        super(location, source, Sort.BAG_ITEM);
    }

    public BagItem(Element element, JavaClassesFactory factory) {
        super(element);
        this.value = (Term) factory.getTerm(XML.getChildrenElements(element).get(0));
    }

    public BagItem(BagItem node) {
        super(node);
    }

    public BagItem(Term node) {
        super(Sort.BAG_ITEM);
        this.value = node;
    }

    public String toString() {
        return this.value.toString();
    }

    public Term getItem() {
        return value;
    }

    public void setItem(Term item) {
        this.value = item;
    }

    @Override
    public BagItem shallowCopy() {
        return new BagItem(this);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}

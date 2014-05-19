// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

public class ListItem extends CollectionItem {
    public ListItem(Element element) {
        super(element);
        this.value = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
    }

    public ListItem(ListItem node) {
        super(node);
    }

    public ListItem(Term node) {
        super("ListItem");
        this.value = node;
    }

    public String toString() {
        return this.value.toString();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
    
    @Override
    public ListItem shallowCopy() {
        return new ListItem(this);
    }

}

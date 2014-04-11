package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

public class ListItem extends CollectionItem {
    public ListItem(Element element) {
        super(element);
        this.value = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
    }

    public ListItem(ATermAppl atm) {
        super(atm);
        value = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));
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
    public <P, R> R accept(Visitor<P, R> visitor, P p) {
        return visitor.visit(this, p);
    }
    
    @Override
    public ListItem shallowCopy() {
        return new ListItem(this);
    }

}

package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import aterm.ATermAppl;

import java.util.Collections;
import java.util.List;


/** Map contents have sort Map or MapItem */
public class Map extends Collection {

    public static final Map EMPTY = new Map(Collections.<Term>emptyList());

    public Map(Element element) {
        super(element);
    }

    public Map(ATermAppl atm) {
        super(atm);
    }

    public Map(String location, String filename) {
        super(location, filename, "Map");
    }

    public Map(Map node) {
        super(node);
    }

    public Map() {
        super("Map");
    }

    public Map(List<Term> col) {
        super("Map", col);
    }

    @Override
    public <P, R> R accept(Visitor<P, R> visitor, P p) {
        return visitor.visit(this, p);
    }
    
    @Override
    public Map shallowCopy() {
        return new Map(this);
    }

}

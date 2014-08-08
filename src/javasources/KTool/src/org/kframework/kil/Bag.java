// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A bag. Contents should be a Cell or BagItem node, or term of sort Bag or
 * BagItem.
 */
public class Bag extends Collection {

    public static final Bag EMPTY = new Bag(Collections.<Term> emptyList());

    public Bag(Location location, Source source) {
        super(location, source, Sort.BAG);
    }

    public Bag(Element element) {
        super(element);
    }

    public Bag(Bag node) {
        super(node);
    }

    public Bag() {
        super(Sort.BAG);
    }

    public Bag(List<Term> col) {
        super(Sort.BAG, col);
    }

    public static Bag flatten(Bag bag) {
        Bag flatBag = bag.shallowCopy();
        flatBag.setContents(new ArrayList<Term>());
        flatten(flatBag.getContents(), bag.getContents());
        return flatBag;
    }

    public static void flatten(List<Term> flatBag, List<Term> nestedBag) {
        for (Term term : nestedBag) {
            if (term instanceof Bag) {
                Bag bag = (Bag) term;
                flatten(flatBag, bag.getContents());
            } else {
                flatBag.add(term);
            }
        }
    }

    @Override
    public String toString() {
        return super.toString();
    }

    @Override
    public Bag shallowCopy() {
        return new Bag(this);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/** Represents a ,, list, as used in KApp */
public class KList extends Collection {

    public static final KList EMPTY = new KList(Collections.<Term> emptyList());

    public KList() {
        super(KSorts.KLIST);
    }

    public KList(String location, String filename) {
        super(location, filename, KSorts.KLIST);
    }

    public KList(Element element) {
        super(element);
    }

    public KList(KList node) {
        super(node);
    }

    public KList(List<Term> col) {
        super(KSorts.KLIST, col);
    }

    public KList(Term ... terms) { this(Arrays.asList(terms)); }

    @Override
    public String toString() {
        String content = "";
        for (int i = 0; i < contents.size(); i++) {
            if (i == contents.size() - 1)
                content += contents.get(i);
            else
                content += contents.get(i) + ",, ";
        }
        return content;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public KList shallowCopy() {
        return new KList(this);
    }

}

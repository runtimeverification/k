// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.Collections;
import java.util.List;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/** Represents the contents (all of sort KItem) joined by ~>. */
public class KSequence extends Collection {

    public static final KSequence EMPTY = new KSequence(Collections.<Term> emptyList());

    public KSequence(Element element) {
        super(element);
    }

    public KSequence(KSequence node) {
        super(node);
    }

    public KSequence() {
        super(Sort.K);
    }

    public KSequence(List<Term> col) {
        super(Sort.K, col);
    }

    @Override
    public String toString() {
        String content = "";
        for (int i = 0; i < contents.size(); i++) {
            if (i == contents.size() - 1)
                content += contents.get(i);
            else
                content += contents.get(i) + "~> ";
        }
        if (content.equals("")) return ".K";
        return content;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public KSequence shallowCopy() {
        return new KSequence(this);
    }
}

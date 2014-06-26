// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import com.google.common.collect.Sets;

import java.util.ArrayList;

/**
 * Used for representing parsing ambiguity. Shouldn't exist after disambiguation.
 */
public class Ambiguity extends Collection {

    public Ambiguity(Element element) {
        super(element);
    }

    public Ambiguity(Ambiguity node) {
        super(node);
    }

    public Ambiguity(String sort, java.util.List<Term> col) {
        super(sort, col);
    }

    public Ambiguity(String sort, java.util.Collection<? extends Term> col) { this(sort, new ArrayList<>(col)); }

    @Override
    public String toString() {
        String content = "";

        for (Term term : contents)
            if (term != null)
                content += term + ",";

        if (content.length() > 1)
            content = content.substring(0, content.length() - 1);

        return "'amb(" + content + ")";
    }

    @Override
    public Ambiguity shallowCopy() {
        return new Ambiguity(this);
    }

    @Override
    public boolean contains(Object o) {
        if (o instanceof Bracket)
            return contains(((Bracket) o).getContent());
        if (o instanceof Cast)
            return contains(((Cast) o).getContent());
        for (int i = 0; i < contents.size(); i++) {
            if (contents.get(i).contains(o)) {
                return true;
            }
        }
        return false;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
    
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Collection other = (Collection) obj;
        if (contents == null) {
            if (other.contents != null)
                return false;
        } else if (!Sets.newHashSet(contents).equals(Sets.newHashSet(other.contents)))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return Sets.newHashSet(contents).hashCode();
    }
}

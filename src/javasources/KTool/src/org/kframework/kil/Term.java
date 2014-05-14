// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;

import org.w3c.dom.Element;

/**
 * Base of all nodes that represent terms in the semantics. Each term is labeled with a sort.
 */
public abstract class Term extends ASTNode implements Comparable<Term> {
    protected String sort;

    protected Term() {
    }

    public Term(Term t) {
        super(t);
        this.sort = t.sort;
    }

    public Term(String location, String filename, String sort) {
        super(location, filename);
        setSort(sort);
    }

    public Term(Element element) {
        super(element);
        this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
    }

    public Term(String sort) {
        super();
        this.sort = sort;
    }

    public String getSort() {
        return sort;
    }

    public void setSort(String sort) {
        this.sort = sort;
    }

    @Override
    public abstract Term shallowCopy();

    public abstract int hashCode();

    public abstract boolean equals(Object obj);

    // This method compares equality based on membership in a parse forest
    public boolean contains(Object obj) {
        return this.equals(obj);
    }

    /**
     * Returns a {@code Set} of {@link Variable} instances occurring in this {@code Term}.
     *
     * @return
     */
    public Set<Variable> variables() {
        final Set<Variable> result = new HashSet<Variable>();
        new BasicVisitor(null) {
            @Override
            public Void visit(Variable node, Void _) {
                result.add(node);
                return null;
            }
        }.visitNode(this);
        return result;
    }

    @Override
    public int compareTo(Term o) {
        return toString().compareTo(o.toString());
    }
}

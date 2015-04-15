// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.loader.Context;

import java.util.HashSet;
import java.util.Set;

import org.w3c.dom.Element;

/**
 * Base of all nodes that represent terms in the semantics. Each term is labeled with a sort.
 */
public abstract class Term extends ASTNode implements Comparable<Term> {
    protected Sort sort;

    protected Term() {
    }

    public Term(Term t) {
        super(t);
        this.sort = t.sort;
    }

    public Term(Location location, Source source, Sort sort) {
        super(location, source);
        setSort(sort);
    }

    public Term(Element element) {
        super(element);
        this.sort = Sort.of(element.getAttribute(Constants.SORT_sort_ATTR));
    }

    public Term(Sort sort) {
        super();
        this.sort = sort;
    }

    public Sort getSort() {
        return sort;
    }

    public void setSort(Sort sort) {
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
        final Set<Variable> result = new HashSet<>();
        new BasicVisitor(null) {
            @Override
            public Void visit(Variable node, Void _void) {
                result.add(node);
                return null;
            }
        }.visitNode(this);
        return result;
    }

    public Set<KLabelConstant> impureFunctions(Context context) {
        final Set<KLabelConstant> result = new HashSet<>();
        new BasicVisitor(context) {
            @Override
            public Void visit(KLabelConstant node, Void _void) {
                boolean isImpure = context.productionsOf(node.getLabel()).stream().anyMatch(p -> p.containsAttribute(Attribute.IMPURE_KEY));
                if (isImpure) {
                    result.add(node);
                }
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

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.HashSet;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.visitors.Visitor;

/** A nonterminal in a {@link Production}. Also abused in some places as a sort identifier */
public class Sort extends ProductionItem {

    public static final String BOOL = "Bool";

    private String name;

    public Sort(String name) {
        super();
        this.name = name;
    }

    public Sort(Sort sort) {
        super(sort);
        this.name = sort.getName();
    }

    @Deprecated
    public static boolean isBasesort(String sort) {
        return Sort2.of(sort).isBaseSort();
    }

    @Deprecated
    public boolean isBaseSort() {
        return Sort.isBasesort(getName());
    }

    public void setName(String sort) {
        this.name = sort;
    }

    public String getName() {
        if (MetaK.isCellSort(name))
            return Sort2.BAG.getName();
        return name;
    }

    public String getRealName() {
        return name;
    }

    @Override
    public String toString() {
        return getName();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (!(obj instanceof Sort))
            return false;

        Sort srt = (Sort) obj;

        if (!getName().equals(srt.getName()))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return this.getName().hashCode();
    }

    @Override
    public Sort shallowCopy() {
        return new Sort(this);
    }
}

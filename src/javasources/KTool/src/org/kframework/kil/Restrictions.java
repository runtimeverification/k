// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/**
 *
 */
public class Restrictions extends ModuleItem {
    Sort sort;
    Terminal terminal;
    String pattern;

    public Sort getSort() {
        return sort;
    }

    public void setSort(Sort sort) {
        this.sort = sort;
    }

    public Restrictions(Sort sort, Terminal terminal, String pattern) {
        this.sort = sort;
        this.terminal = terminal;
        this.pattern = pattern;
    }

    public Restrictions(Restrictions node) {
        super(node);
        this.sort = node.sort;
        this.terminal = node.terminal;
        this.pattern = node.pattern;
    }

    @Override
    public String toString() {
        return "  syntax " + (sort != null ? sort : terminal) + " -/- " + pattern + "\n";
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof Restrictions))
            return false;
        Restrictions syn = (Restrictions) obj;
        if (!pattern.equals(syn.pattern))
            return false;

        if (!(sort != null ? sort.equals(syn.sort) : terminal.equals(syn.terminal)))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        int hash = pattern.hashCode();
        hash += sort != null ? sort.hashCode() : terminal.hashCode();
        return hash;
    }

    @Override
    public Restrictions shallowCopy() {
        return new Restrictions(this);
    }

    public Terminal getTerminal() {
        return terminal;
    }

    public void setTerminal(Terminal terminal) {
        this.terminal = terminal;
    }

    public String getPattern() {
        return pattern;
    }

    public void setPattern(String pattern) {
        this.pattern = pattern;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}

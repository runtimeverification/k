// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kore.Sort;

import scala.Option;

import java.util.Optional;

/** A nonterminal in a {@link Production}. Also abused in some places as a sort identifier */
public class NonTerminal extends ProductionItem {

    private Sort sort;
    private Optional<String> name;

    public NonTerminal(Sort sort, Optional<String> name) {
        super();
        this.sort = sort;
        this.name = name;
    }

    public NonTerminal(NonTerminal nonTerminal) {
        super(nonTerminal);
        this.sort = nonTerminal.sort;
        this.name = nonTerminal.name;
    }

    public Option<String> getName() {
        if (name.isPresent()) {
            return Option.apply(name.get());
        }
        return Option.empty();
    }

    public void setSort(Sort sort) {
        this.sort = sort;
    }

    public Sort getSort() {
        return sort;
    }

    public Sort getRealSort() {
        return sort;
    }

    @Override
    public String toString() {
        return sort.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (!(obj instanceof NonTerminal))
            return false;

        NonTerminal nt = (NonTerminal) obj;

        if (!sort.equals(nt.sort))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return sort.hashCode();
    }

    @Override
    public NonTerminal shallowCopy() {
        return new NonTerminal(this);
    }
}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;


/**
 * @author AndreiS
 */
public class TokenIndex implements Index {

    private final String sort;

    public TokenIndex(String sort) {
        this.sort = sort;
    }
    
    public String sort() {
        return sort;
    }

    @Override
    public boolean isUnifiable(Index index) {
        return index instanceof TopIndex || equals(index);
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof TokenIndex)) {
            return false;
        }

        TokenIndex index = (TokenIndex) object;
        return sort.equals(index.sort);
    }

    @Override
    public int hashCode() {
        return sort.hashCode();
    }

    @Override
    public String toString() {
        return "@" + sort;
    }

}

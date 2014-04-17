// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.backend.java.util.Utils;
import org.kframework.kil.visitors.Visitor;

/**
 * @author AndreiS
 */
public class KItemProjection extends Term {

    private Term term;

    public KItemProjection(String kind, Term term) {
        super(kind);
        this.term = term;
    }

    public KItemProjection(KItemProjection kItemProjection){
        super(kItemProjection);
        this.term = kItemProjection.term;
    }

    public Term getTerm() {
        return term;
    }

    public String projectedKind() {
        return getSort();
    }

    public void setTerm(Term term) {
        this.term = term;
    }
    
    @Override
    public KItemProjection shallowCopy() {
        return new KItemProjection(this);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + getSort().hashCode();
        hash = hash * Utils.HASH_PRIME + term.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KItemProjection)) {
            return false;
        }
        KItemProjection kItemProjection = (KItemProjection) object;

        return getSort().equals(kItemProjection.getSort()) && term.equals(kItemProjection.term);
    }
    
    @Override
    public String toString() {
        return "projection(" + term + ")";
    }

    @Override
    public <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.visit(this, p);
    }
}

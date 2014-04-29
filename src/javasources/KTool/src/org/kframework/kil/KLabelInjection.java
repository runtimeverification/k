// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;


/**
 * @author AndreiS
 */
public class KLabelInjection extends KLabel implements Interfaces.MutableParent<Term, Enum<?>> {

    private Term term;

    public KLabelInjection(Term term) {
        setTerm(term);
    }

    public KLabelInjection(KLabelInjection kLabelInjection) {
        this(kLabelInjection.term);
    }

    public Term getTerm() {
        return term;
    }

    public String injectedKind() {
        return term.getSort();
    }

    public void setTerm(Term term) {
        // TODO(AndreiS): fix assertion
        //assert term.getSort().equals(KSorts.K) || term.getSort().equals(KSorts.KLABEL)
        //       || term.getSort().equals(KSorts.KLIST);
        this.term = term;
    }
    
    @Override
    public String toString() {
        return "(# " + term + ")";
    }

    @Override
    public KLabelInjection shallowCopy() {
        return new KLabelInjection(this);
    }

    @Override
    public int hashCode() {
        return term.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KLabelInjection)) {
            return false;
        }
        KLabelInjection kLabelInjection = (KLabelInjection) object;

        return term.equals(kLabelInjection.term);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Term getChild(Enum<?> type) {
        return term;
    }

    @Override
    public void setChild(Term child, Enum<?> type) {
        this.term = child;
    }
}

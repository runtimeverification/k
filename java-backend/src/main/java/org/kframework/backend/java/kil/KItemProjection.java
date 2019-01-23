// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;


/**
 * @author AndreiS
 */
public class KItemProjection extends Term {

    // TODO(YilongL): can we enforce this to be a KItem?
    private final Term term;

    public KItemProjection(Kind kind, Term term) {
        super(kind);
        this.term = term;
    }

    public Term evaluateProjection() {
        // TODO(AndreiS): hack until new KORE makes this class obsolete
        if (!term.sort().equals(Sort.KITEM) && !term.sort().equals(Sort.BAG)) {
            return term;
        }

        if (!(term instanceof KItem)) {
            return this;
        }

        if (!(((KItem) term).kLabel() instanceof KLabelInjection)) {
            return this;
        }

        if (!(((KItem) term).kList() instanceof KList)
                || ((KList) ((KItem) term).kList()).concreteSize() != 0
                || ((KList) ((KItem) term).kList()).hasFrame()) {
            return this;
        }

        return ((KLabelInjection) ((KItem) term).kLabel()).term();
    }

    public Term term() {
        return term;
    }

    @Override
    public boolean isExactSort() {
        return false;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public Sort sort() {
        return kind.asSort();
    }

    @Override
    protected int computeHash() {
        return term.hashCode();
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
        return term.equals(kItemProjection.term);
    }

    @Override
    public String toString() {
        return "projection(" + term + ")";
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

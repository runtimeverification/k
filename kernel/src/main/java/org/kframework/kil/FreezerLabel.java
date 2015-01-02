// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/*
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 2/5/13
 * Time: 5:58 PM
 */
/**
 * Represents a term of sort KLabel made by injecting a Freezer
 * Corresponds to operator and #freezer_ in source.
 * Usually only occurs as the label of a {@link KApp} an {@link Empty} as arguments.
 */
public class FreezerLabel extends KInjectedLabel {
    public FreezerLabel(Location location, Source source) {
        super(location, source);
    }

    public FreezerLabel(FreezerLabel l) {
        super(l);
    }

    @Override
    public FreezerLabel shallowCopy() {
        return new FreezerLabel(this);
    }

    public FreezerLabel(Term t) {
        super(t);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}

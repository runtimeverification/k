// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

import java.util.Collection;

/**
 * A builtin set
 *
 * @author TraianSF
 */
public class SetBuiltin extends CollectionBuiltin {
    public SetBuiltin(DataStructureSort sort, Collection<Term> baseTerms, java.util.Collection<Term> elements) {
        super(sort, baseTerms, elements);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
    
    @Override
    public DataStructureBuiltin shallowCopy(Collection<Term> baseTerms) {
        return new SetBuiltin(sort(), baseTerms, elements());
    }
    
    @Override
    public CollectionBuiltin shallowCopy(Collection<Term> baseTerms,
            Collection<Term> elements) {
        return new SetBuiltin(sort(), baseTerms, elements);
    }
}

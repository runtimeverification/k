// Copyright (c) 2014-2016 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

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

    @Override
    public Term toKApp(Context context, Comparator<Term> comparator) {
        List<Term> items = new ArrayList<>();
        for (Term element : elements()) {
            Term item = KApp.of(element.getLocation(), element.getSource(), sort().elementLabel(), element);
            items.add(item);
        }
        for (Term base : baseTerms()) {
            items.add(base);
        }
        Collections.sort(items, comparator);
        return toKApp(items);
    }
}

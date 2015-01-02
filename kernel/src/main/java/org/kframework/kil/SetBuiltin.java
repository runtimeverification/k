// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.backend.unparser.UnparserLexicalComparator;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
    public Term toKApp(Context context) {
        List<Term> items = new ArrayList<>();
        Map<Term, String> unparsed = new HashMap<>();
        for (Term element : elements()) {
            Term item = KApp.of(sort().elementLabel(), element);
            items.add(item);
            UnparserFilter unparser = new UnparserFilter(context);
            unparser.visitNode(item);
            String s = unparser.getResult();
            unparsed.put(item, s);
        }
        Collections.sort(items, new UnparserLexicalComparator(unparsed));
        for (Term base : baseTerms()) {
            items.add(base);
        }
        return toKApp(items);
    }
}

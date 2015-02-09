// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.kframework.parser.KList;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import java.util.ArrayList;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
// TODO: simplify by removing leftover "null" checks and recheck this code
public class TreeCleanerVisitor extends CatchTransformer {

    @Override
    public boolean cache() {
        return true;
    }

    @Override
    public Term apply(TermCons tc) throws ParseFailedException {
        if (!tc.production().klabel().isDefined()) {
            // eliminating syntactic subsort
            if (tc.items().size() != 1)
                throw  new ParseFailedException(new KException(
                        KException.ExceptionType.ERROR, KException.KExceptionGroup.INNER_PARSER,
                        "Only subsort productions are allowed to have no #klabel attribute", null, null));
            //TODO: add source and location to error
            return super.apply(tc.items().get(0));
        } else {
            // invalidate the hashCode cache
            tc.invalidateHashCode();
            return super.apply(tc);
        }
    }

    /**
     * Remove KList artifacts from parsing only they contain only one element.
     */
    @Override
    public Term apply(KList node) throws ParseFailedException {
        java.util.List<Term> contents = new ArrayList<>();
        for (Term t : node.items()) {
            Term transformed = super.apply(t);
            if (transformed != null)
                contents.add(transformed);
        }
        node.replaceChildren(contents);
        if (contents.size() == 0)
            return KList.apply();
        else if(contents.size() == 1)
            return contents.get(0);
        else
            return node;
    }
}

// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import java.util.HashSet;
import java.util.Set;

import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.parser.Transformer;
import org.kframework.utils.errorsystem.ParseFailedException;

import scala.util.Either;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
// TODO: simplify by removing leftover "null" checks and recheck this code
public class TreeCleanerVisitor extends Transformer<Set<ParseFailedException>> {

    @Override
    public Either<Set<ParseFailedException>, Term> apply(TermCons tc) {
        Either<Set<ParseFailedException>, Term> vis;
        if (tc.production().klabel().isEmpty())
            // elimnating syntactic subsort
            vis = apply(tc.items().get(0));
        else {
            // invalidate the hashCode cache
//            tc.invalidateHashCode();
            vis = super.apply(tc);
        }
        return vis;
    }

    public Set<ParseFailedException> merge(Set<ParseFailedException> a, Set<ParseFailedException> b) {
        Set<ParseFailedException> ret = new HashSet<>(a);
        ret.addAll(b);
        return ret;
    }
}

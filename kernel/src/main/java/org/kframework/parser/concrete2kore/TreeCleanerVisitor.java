// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import com.google.common.collect.Sets;
import org.kframework.parser.KList;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.parser.TransformerWithErrors;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
public class TreeCleanerVisitor extends TransformerWithErrors<Set<ParseFailedException>> {
    @Override
    public Either<Set<ParseFailedException>, Term> apply(TermCons tc) {
        Either<Set<ParseFailedException>, Term> vis;
        if (tc.production().klabel().isEmpty()) {
            // eliminating syntactic subsort
            if (tc.items().size() != 1)
                return Left.apply(Sets.newHashSet(new ParseFailedException(new KException(
                        KException.ExceptionType.ERROR, KException.KExceptionGroup.INNER_PARSER,
                        "Only subsort productions are allowed to have no #klabel attribute", null, null))));
            //TODO: add source and location to error
            vis = apply(tc.items().get(0));
        } else {
            // invalidate the hashCode cache
            tc.invalidateHashCode();
            vis = super.apply(tc);
        }
        return vis;
    }

    /**
     * Remove KList artifacts from parsing only they contain only one element.
     */
    @Override
    public Either<Set<ParseFailedException>, Term> apply(KList node) {
        Either<Set<ParseFailedException>, Term> res = super.apply(node);

        if (res.isRight() && ((KList) res.right().get()).items().size() == 1)
            return Right.apply(((KList) res.right().get()).items().get(0));
        else
            return res;
    }

    public Set<ParseFailedException> mergeErrors(Set<ParseFailedException> a, Set<ParseFailedException> b) {
        return Sets.union(a, b);
    }

    @Override
    public Set<ParseFailedException> errorUnit() {
        return new LinkedHashSet<>();
    }
}

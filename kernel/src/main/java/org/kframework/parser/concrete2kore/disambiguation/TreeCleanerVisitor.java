// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.parser.KList;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.Set;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
public class TreeCleanerVisitor extends SetsTransformerWithErrors<ParseFailedException> {
    @Override
    public Either<Set<ParseFailedException>, Term> apply(TermCons tc) {
        Either<Set<ParseFailedException>, Term> vis;
        if (tc.production().isSyntacticSubsort() && tc.production().klabel().isEmpty()) {
            // eliminating syntactic subsort
            vis = apply(tc.get(0));
        } else if (!tc.production().att().contains("bracket") && tc.production().klabel().isEmpty()) {
            return Left.apply(Sets.newHashSet(new ParseFailedException(new KException(
                    KException.ExceptionType.ERROR, KException.KExceptionGroup.INNER_PARSER,
                    "Only subsort productions are allowed to have no #klabel attribute", tc.source().get(), tc.location().get()))));
            //TODO: add source and location to error
        } else {
            // invalidate the hashCode cache
            vis = super.apply(tc);
        }
        return vis;
    }

    /**
     * Remove KList artifacts from parsing only when it contains a single element.
     */
    @Override
    public Either<Set<ParseFailedException>, Term> apply(KList node) {
        Either<Set<ParseFailedException>, Term> res = super.apply(node);

        if (res.isRight() && ((KList) res.right().get()).items().size() == 1)
            return Right.apply(((KList) res.right().get()).items().get(0));
        else
            return res;
    }
}

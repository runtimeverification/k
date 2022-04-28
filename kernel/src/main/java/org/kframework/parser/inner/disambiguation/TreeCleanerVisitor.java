// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.attributes.Att;
import org.kframework.parser.KList;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.Set;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
public class TreeCleanerVisitor extends SetsTransformerWithErrors<KEMException> {
    @Override
    public Either<Set<KEMException>, Term> apply(TermCons tc) {
        Either<Set<KEMException>, Term> vis;
        if (tc.production().isSyntacticSubsort() && tc.production().klabel().isEmpty()) {
            // eliminating syntactic subsort
            vis = apply(tc.get(0));
        } else if (!tc.production().att().contains(Att.BRACKET()) && tc.production().klabel().isEmpty()) {
            return Left.apply(Sets.newHashSet(KEMException.innerParserError(
                    "Only subsort productions are allowed to have no #klabel attribute", tc)));
        } else {
            // invalidate the hashCode cache
            vis = super.apply(tc);
        }
        return vis;
    }
}

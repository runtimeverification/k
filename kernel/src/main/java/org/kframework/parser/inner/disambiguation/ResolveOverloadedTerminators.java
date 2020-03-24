// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.attributes.Att;
import org.kframework.definition.Production;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;
import java.util.stream.Collectors;

import scala.util.Either;
import scala.util.Left;

import static org.kframework.Collections.*;

public class ResolveOverloadedTerminators extends SetsTransformerWithErrors<KEMException> {

    private final POSet<Production> overloads;

    public ResolveOverloadedTerminators(POSet<Production> overloads) {
        this.overloads = overloads;
    }

    @Override
    public Either<Set<KEMException>, Term> apply(TermCons tc) {
        if (overloads.elements().contains(tc.production()) && tc.items().isEmpty()) {
            Set<Production> candidates = stream(overloads.elements()).filter(p -> p.klabel().isDefined() && p.klabelAtt().equals(tc.production().klabelAtt()) && overloads.lessThanEq(p, tc.production())).collect(Collectors.toSet());
            candidates = overloads.minimal(candidates);
            if (candidates.size() != 1) {
                String msg = "Overloaded term does not have a least sort. Possible sorts: " + candidates;
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
            }
            Production prod = candidates.iterator().next();
            prod = prod.withAtt(prod.att()
                    .add(Att.ORIGINAL_PRD(), Production.class, tc.production()));
            return super.apply(TermCons.apply(tc.items(), prod, tc.location(), tc.source()));
        }
        return super.apply(tc);
    }
}

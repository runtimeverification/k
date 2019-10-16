// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Production;
import org.kframework.kil.loader.Constants;
import org.kframework.kore.KLabel;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import scala.util.Either;
import scala.util.Left;

import static org.kframework.definition.Constructors.*;
import static org.kframework.Collections.*;

public class ResolveOverloadedTerminators extends SetsTransformerWithErrors<ParseFailedException> {

    private final POSet<Production> overloads;

    public ResolveOverloadedTerminators(POSet<Production> overloads) {
        this.overloads = overloads;
    }

    @Override
    public Either<Set<ParseFailedException>, Term> apply(TermCons tc) {
        if (overloads.elements().contains(tc.production()) && tc.items().isEmpty()) {
            Set<Production> candidates = stream(overloads.elements()).filter(p -> p.klabel().isDefined() && p.klabelAtt().equals(tc.production().klabelAtt()) && overloads.lessThanEq(p, tc.production())).collect(Collectors.toSet());
            candidates = overloads.minimal(candidates);
            if (candidates.size() != 1) {
                KException ex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.INNER_PARSER, "Overloaded term does not have a least sort. Possible sorts: " + candidates, tc.source().orElse(null), tc.location().orElse(null));
                return Left.apply(Sets.newHashSet(new ParseFailedException(ex)));
            }
            Production prod = candidates.iterator().next();
            prod = prod.withAtt(prod.att()
                    .add(Constants.ORIGINAL_PRD, Production.class, tc.production()));
            return super.apply(TermCons.apply(tc.items(), prod, tc.location(), tc.source()));
        }
        return super.apply(tc);
    }
}

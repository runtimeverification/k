// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.parser.SetsGeneralTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Tuple2;
import scala.util.Either;


/**
 * Apply the priority and associativity filters.
 */
public class VariableTypeInferenceFilter extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {

    @Override
    public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<ParseFailedException>> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;

        return super.apply(tc);
    }
}

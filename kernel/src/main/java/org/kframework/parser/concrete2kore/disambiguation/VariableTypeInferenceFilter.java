// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.parser.GeneralTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Tuple2;
import scala.util.Either;

import java.util.LinkedHashSet;


/**
 * Apply the priority and associativity filters.
 */
public class VariableTypeInferenceFilter extends GeneralTransformer<java.util.Set<ParseFailedException>, java.util.Set<ParseFailedException>> {

    @Override
    public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<ParseFailedException>> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;

        return super.apply(tc);
    }

    public java.util.Set<ParseFailedException> mergeErrors(java.util.Set<ParseFailedException> a, java.util.Set<ParseFailedException> b) {
        return Sets.union(a, b);
    }

    @Override
    public java.util.Set<ParseFailedException> mergeWarnings(java.util.Set<ParseFailedException> a, java.util.Set<ParseFailedException> b) {
        return Sets.union(a, b);
    }

    @Override
    public java.util.Set<ParseFailedException> errorUnit() {
        return new LinkedHashSet<>();
    }

    @Override
    public java.util.Set<ParseFailedException> warningUnit() {
        return new LinkedHashSet<>();
    }
}

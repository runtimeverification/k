// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.kore.K;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SetsGeneralTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Right;

import java.util.Set;

/**
 * Eliminate remaining ambiguities by choosing one of them.
 */
public class AmbFilter extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {

    private final boolean strict;

    public AmbFilter(boolean strict) {
        this.strict = strict;
    }

    @Override
    public Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> apply(Ambiguity amb) {
        K last = null;
        boolean equal = true;
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> candidate = null;
        for (Term t : amb.items()) {
            candidate = this.apply(t);
            K next = new TreeNodesToKORE(Outer::parseSort, strict).apply(new RemoveBracketVisitor().apply(candidate._1().right().get()));
            if (last != null) {
                if (!last.equals(next)) {
                    equal = false;
                    break;
                }
            }
            last = next;
        }
        if(equal) {
            // all ambiguities have the same abstract syntax, so just pick one
            return candidate;
        }

        String msg = "Parsing ambiguity. Arbitrarily choosing the first.";

        for (int i = 0; i < amb.items().size(); i++) {
            msg += "\n" + (i + 1) + ": ";
            Term elem = (Term) amb.items().toArray()[i];
            if (elem instanceof ProductionReference) {
                ProductionReference tc = (ProductionReference) elem;
                msg += tc.production().toString();
            }
            // TODO: use the unparser
            //Unparser unparser = new Unparser(context);
            //msg += "\n   " + unparser.print(elem).replace("\n", "\n   ");
            msg += "\n    " + new RemoveBracketVisitor().apply(elem);
        }
        // TODO: add location information
        ParseFailedException w = new ParseFailedException(
                new KException(ExceptionType.WARNING, KExceptionGroup.INNER_PARSER, msg, amb.items().iterator().next().source().get(), amb.items().iterator().next().location().get()));

        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rez = this.apply(amb.items().iterator().next());
        return new Tuple2<>(Right.apply(rez._1().right().get()), Sets.union(Sets.newHashSet(w), rez._2()));
    }
}

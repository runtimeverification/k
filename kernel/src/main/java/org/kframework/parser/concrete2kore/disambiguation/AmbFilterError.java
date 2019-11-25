// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.kore.K;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.util.Either;
import scala.util.Left;

import java.util.Set;

/**
 * Report remaining ambiguities as errors.
 */
public class AmbFilterError extends SetsTransformerWithErrors<ParseFailedException> {

    private final boolean strict;

    public AmbFilterError(boolean strict) {
        this.strict = strict;
    }

    @Override
    public Either<Set<ParseFailedException>, Term> apply(Ambiguity amb) {
        K last = null;
        boolean equal = true;
        Either<Set<ParseFailedException>, Term> candidate = null;
        for (Term t : amb.items()) {
            candidate = this.apply(t);
            if (candidate.isLeft()) {
              return candidate;
            }
            K next = new TreeNodesToKORE(Outer::parseSort, strict).apply(new RemoveBracketVisitor().apply(candidate.right().get()));
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

        String msg = "Parsing ambiguity.";

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

        ParseFailedException e = new ParseFailedException(
                new KException(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, msg, amb.items().iterator().next().source().get(), amb.items().iterator().next().location().get()));

        return Left.apply(Sets.newHashSet(e));
    }
}

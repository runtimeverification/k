// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.kore.K;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import scala.util.Either;
import scala.util.Left;

import java.util.Set;

/**
 * Report remaining ambiguities as errors.
 */
public class AmbFilterError extends SetsTransformerWithErrors<KEMException> {

    private final boolean strict;

    public AmbFilterError(boolean strict) {
        this.strict = strict;
    }

    @Override
    public Either<Set<KEMException>, Term> apply(Ambiguity amb) {
        K last = null;
        boolean equal = true;
        Either<Set<KEMException>, Term> candidate = null;
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

        KEMException e = KEMException.innerParserError(msg, amb.items().iterator().next());

        return Left.apply(Sets.newHashSet(e));
    }
}

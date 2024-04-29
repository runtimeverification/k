// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import java.util.List;
import java.util.Set;
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

/** Report remaining ambiguities as errors. */
public class AmbFilterError extends SetsTransformerWithErrors<KEMException> {

  public AmbFilterError() {}

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
      K next =
          new TreeNodesToKORE(Outer::parseSort)
              .apply(new RemoveBracketVisitor().apply(candidate.right().get()));
      if (last != null) {
        if (!last.equals(next)) {
          equal = false;
          break;
        }
      }
      last = next;
    }
    if (equal) {
      // all ambiguities have the same abstract syntax, so just pick one
      return candidate;
    }

    StringBuilder msg = new StringBuilder("Parsing ambiguity.");

    List<Term> sortedItems = amb.items().stream().sorted(Term.ord()).toList();
    for (int i = 0; i < sortedItems.size(); i++) {
      msg.append("\n").append(i + 1).append(": ");
      Term elem = sortedItems.get(i);
      if (elem instanceof ProductionReference tc) {
        msg.append(tc.production().toString());
      }
      // TODO: use the unparser
      // Unparser unparser = new Unparser(context);
      // msg += "\n   " + unparser.print(elem).replace("\n", "\n   ");
      msg.append("\n    ").append(new RemoveBracketVisitor().apply(elem));
    }

    KEMException e = KEMException.innerParserError(msg.toString(), amb.items().iterator().next());

    return Left.apply(Sets.newHashSet(e));
  }
}

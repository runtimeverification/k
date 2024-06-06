// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import java.util.HashSet;
import java.util.Set;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;

/**
 * A transformer which merges nested Ambiguities. For example, amb(amb(a, amb(b, c)), d) is
 * transformed into amb(a, b, c, d).
 */
public class AmbiguityMergingTransformer extends SafeTransformer {
  @Override
  public final Term apply(Ambiguity amb) {
    Set<Term> items = new HashSet<>();
    for (Term item : amb.items()) {
      item = apply(item);
      if (item instanceof Ambiguity nestedAmb) {
        items.addAll(nestedAmb.items());
      } else {
        items.add(item);
      }
    }
    return Ambiguity.apply(items);
  }
}

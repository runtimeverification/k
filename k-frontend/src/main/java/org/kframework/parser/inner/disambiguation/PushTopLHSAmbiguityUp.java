// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import java.util.HashSet;
import java.util.Set;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

/**
 * A transformer which ensures that the LHS of any top-level rewrite is not an Ambiguity. If such an
 * Ambiguity is present, it is pushed above the containing #RuleContent.
 *
 * <p>This simplifies sort inference for non-widening rules, where inference must readily know the
 * declared sort of a rule's LHS.
 */
public class PushTopLHSAmbiguityUp extends AmbiguityMergingTransformer {
  private static Term pushChildAmbiguityUp(TermCons tc) {
    if (tc.get(0) instanceof Ambiguity childAmb) {
      Set<Term> items = new HashSet<>();
      for (Term childItem : childAmb.items()) {
        items.add(tc.with(0, childItem));
      }
      return Ambiguity.apply(items);
    }
    return tc;
  }

  @Override
  public Term apply(TermCons tc) {
    /*
     * The syntax for #RuleContent is given by
     *
     *
     * syntax #RuleContent ::= #RuleBody
     *                       | #RuleBody "requires" Bool
     *                       | #RuleBody "when" Bool
     *                       | #RuleBody "ensures"  Bool
     *                       | #RuleBody "requires" Bool "ensures" Bool
     *                       | #RuleBody "when" Bool "ensures" Bool
     *
     * where the production `syntax #RuleContent ::= #RuleBody` is given a klabel and thus is
     * explicitly represented by a TermCons. In any case then, we look for ambiguities in
     * the 0th child.
     */
    if (tc.production().sort().equals(Sorts.RuleContent())) {
      return pushChildAmbiguityUp(tc.with(0, new PushRuleBodyAmbiguityUp().apply(tc.get(0))));
    }
    return super.apply(tc);
  }

  private static class PushRuleBodyAmbiguityUp extends AmbiguityMergingTransformer {
    @Override
    public Term apply(TermCons tc) {
      /*
       * The syntax for #RuleBody is given by
       *
       * syntax #RuleBody ::= K
       *                    | "[" "[" K "]" "]" Bag
       *
       * where the production `syntax #RuleBody ::= K` is NOT given a klabel, so it will NOT be
       * represented explicitly as a TermCons.
       *
       * Thus, either the given TermCons itself could be a top-level rewrite, or it has declared
       * sort #RuleBody and its 0th child could be a top-level rewrite.
       */
      if (tc.production().sort().equals(Sorts.RuleBody())) {
        return pushChildAmbiguityUp(tc.with(0, new PushLHSRewriteAmbiguityUp().apply(tc.get(0))));
      }
      return new PushLHSRewriteAmbiguityUp().apply(tc);
    }
  }

  private static class PushLHSRewriteAmbiguityUp extends AmbiguityMergingTransformer {
    @Override
    public Term apply(TermCons tc) {
      if (tc.production().klabel().isDefined()
          && tc.production().klabel().get().head().equals(KLabels.KREWRITE)) {
        return pushChildAmbiguityUp(tc);
      }
      return tc;
    }
  }
}

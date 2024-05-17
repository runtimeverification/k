// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.kore.KORE.*;

import java.util.Arrays;
import org.junit.Assert;
import org.junit.Test;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.KApply;

public class EliminateOrPatternsTest {
  private static KApply term(String name, K... disjuncts) {
    return KApply(KLabel(name), KList(Arrays.stream(disjuncts).toList()));
  }

  private static KApply or(K... disjuncts) {
    return KApply(KLabels.ML_OR, KList(Arrays.stream(disjuncts).toList()));
  }

  private static KApply rhs() {
    return term("rhs");
  }

  private static Rule ruleFromLHS(K lhs) {
    return new Rule(KRewrite(lhs, rhs()), BooleanUtils.TRUE, BooleanUtils.TRUE, Att.empty());
  }

  @Test
  public void testVariable() {
    Rule r = ruleFromLHS(KVariable("X"));

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(1, result.size());
    Assert.assertTrue(result.contains(r));
  }

  @Test
  public void testTerm() {
    Rule r = ruleFromLHS(KApply(KLabel("a")));

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(1, result.size());
    Assert.assertTrue(result.contains(r));
  }

  @Test
  public void testApply() {
    Rule r = ruleFromLHS(term("foo", term("a"), term("b")));

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(1, result.size());
    Assert.assertTrue(result.contains(r));
  }

  @Test
  public void testSingleOr() {
    Rule r = ruleFromLHS(term("foo", or(term("a"), term("b"))));

    Rule aRule = ruleFromLHS(term("foo", term("a")));
    Rule bRule = ruleFromLHS(term("foo", term("b")));

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(2, result.size());
    Assert.assertTrue(result.containsAll(Arrays.asList(aRule, bRule)));
  }

  @Test
  public void testTwoOrs() {
    Rule r = ruleFromLHS(term("foo", or(term("a"), term("b")), or(term("c"), term("d"))));

    Rule acRule = ruleFromLHS(term("foo", term("a"), term("c")));
    Rule adRule = ruleFromLHS(term("foo", term("a"), term("d")));
    Rule bcRule = ruleFromLHS(term("foo", term("b"), term("c")));
    Rule bdRule = ruleFromLHS(term("foo", term("b"), term("d")));

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(4, result.size());
    Assert.assertTrue(result.containsAll(Arrays.asList(acRule, adRule, bcRule, bdRule)));
  }

  @Test
  public void testNestedOr() {
    Rule r = ruleFromLHS(term("foo", or(term("a"), or(term("b"), term("c")))));

    Rule aRule = ruleFromLHS(term("foo", term("a")));
    Rule bRule = ruleFromLHS(term("foo", term("b")));
    Rule cRule = ruleFromLHS(term("foo", term("c")));

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(3, result.size());
    Assert.assertTrue(result.containsAll(Arrays.asList(aRule, bRule, cRule)));
  }

  @Test
  public void testAs() {
    Rule r = ruleFromLHS(term("foo", KAs(or(term("a"), term("b")), KVariable("X"))));

    Rule aRule = ruleFromLHS(term("foo", KAs(term("a"), KVariable("X"))));
    Rule bRule = ruleFromLHS(term("foo", KAs(term("b"), KVariable("X"))));

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(2, result.size());
    Assert.assertTrue(result.containsAll(Arrays.asList(aRule, bRule)));
  }

  @Test
  public void testLifting() {
    K body = term("foo", term("bar", KRewrite(or(term("a"), term("b")), term("c"))));

    Rule r = new Rule(body, BooleanUtils.TRUE, BooleanUtils.TRUE, Att.empty());

    K liftedRhs = term("foo", term("bar", term("c")));

    Rule aRule =
        new Rule(
            KRewrite(term("foo", term("bar", term("a"))), liftedRhs),
            BooleanUtils.TRUE,
            BooleanUtils.TRUE,
            Att.empty());
    Rule bRule =
        new Rule(
            KRewrite(term("foo", term("bar", term("b"))), liftedRhs),
            BooleanUtils.TRUE,
            BooleanUtils.TRUE,
            Att.empty());

    var result = EliminateOrPatterns.expand(r);
    Assert.assertEquals(2, result.size());
    Assert.assertTrue(result.containsAll(Arrays.asList(aRule, bRule)));
  }
}

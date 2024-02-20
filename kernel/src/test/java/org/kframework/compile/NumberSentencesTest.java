// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import org.junit.Test;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Rule;

public class NumberSentencesTest {

  private static final List<Att> testAtts =
      Arrays.asList(
          Att.empty(),
          Att.empty().add(Att.ANYWHERE()),
          Att.empty().add(Att.CONCRETE(), "A"),
          Att.empty().add(Att.CONCRETE(), "B"),
          Att.empty().add(Att.NON_EXECUTABLE()),
          Att.empty().add(Att.OWISE()),
          Att.empty().add(Att.PRIORITY(), "50"),
          Att.empty().add(Att.PRIORITY(), "100"),
          Att.empty().add(Att.SIMPLIFICATION()),
          Att.empty().add(Att.SYMBOLIC(), "A"),
          Att.empty().add(Att.SYMBOLIC(), "B"));

  @Test
  public void testHash() {
    Rule r =
        new Rule(
            KRewrite(KApply(KLabel("foo")), KApply(KLabel("bar"))),
            BooleanUtils.TRUE,
            BooleanUtils.TRUE,
            Att.empty());

    List<String> ruleHashes =
        testAtts.stream()
            .map(att -> NumberSentences.number(r.withAtt(att)).att().get(Att.UNIQUE_ID()))
            .collect(Collectors.toList());

    Set<String> uniqueHashes = ruleHashes.stream().collect(Collectors.toSet());

    assertEquals(ruleHashes.size(), uniqueHashes.size());
  }
}

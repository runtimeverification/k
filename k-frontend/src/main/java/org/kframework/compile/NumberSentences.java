// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import java.util.Arrays;
import java.util.List;
import org.bouncycastle.jcajce.provider.digest.SHA3;
import org.bouncycastle.util.encoders.Hex;
import org.kframework.attributes.Att;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;

public class NumberSentences {

  private static final List<Att.Key> preservedAtts =
      Arrays.asList(
          Att.CONCRETE(),
          Att.SYMBOLIC(),
          Att.OWISE(),
          Att.PRIORITY(),
          Att.SIMPLIFICATION(),
          Att.ANYWHERE(),
          Att.NON_EXECUTABLE());

  public static Sentence number(Sentence s) {
    if (!(s instanceof RuleOrClaim) || s.att().contains(Att.UNIQUE_ID())) {
      return s;
    }

    /* Keep the attributes that have an effect on semantics */
    Att a =
        preservedAtts.stream()
            .filter(att -> s.att().contains(att))
            .map(att -> Att.empty().add(att, s.att().get(att)))
            .reduce(Att.empty(), (acc, elem) -> acc.addAll(elem));

    String id = ruleHash(s.withAtt(a));
    return s.withAtt(s.att().add(Att.UNIQUE_ID(), id));
  }

  private static String ruleHash(Sentence s) {
    String text = new NormalizeVariables().normalize(s).toString();
    SHA3.Digest256 sha3engine = new SHA3.Digest256();
    byte[] digest = sha3engine.digest(text.getBytes());
    String digestString = Hex.toHexString(digest);
    return digestString;
  }
}

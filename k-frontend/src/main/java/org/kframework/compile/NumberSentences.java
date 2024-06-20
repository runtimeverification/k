// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.List;
import org.kframework.attributes.Att;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;

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
            .reduce(Att.empty(), Att::addAll);

    String id = ruleHash(s.withAtt(a));
    return s.withAtt(s.att().add(Att.UNIQUE_ID(), id));
  }

  private static String ruleHash(Sentence s) {
    try {
      String text = new NormalizeVariables().normalize(s).toString();
      byte[] digest = MessageDigest.getInstance("SHA3-256").digest(text.getBytes());
      return HexFormat.of().formatHex(digest);
    } catch (NoSuchAlgorithmException e) {
      // This exception should never actually be thrown in practice; it's just a limitation of the
      // Java cryptography APIs that we need to request algorithms by constant string keys and cope
      // with them potentially not existing. SHA3-256 is part of the Java standard library from JDK
      // 17 onwards.
      throw KEMException.criticalError("Error computing rule digest (SHA3-256 unavailable)", e);
    }
  }
}

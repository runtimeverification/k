// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.bouncycastle.jcajce.provider.digest.SHA3;
import org.bouncycastle.util.encoders.Hex;
import org.kframework.attributes.Att;
import org.kframework.definition.Sentence;

public class NumberSentences {
    public Sentence number(Sentence s) {
      return s.withAtt(s.att().add("UNIQUE_ID", ruleHash(s.withAtt(Att.empty()))));
    }

    private String ruleHash(Sentence s) {
      String text = new NormalizeVariables().normalize(s).toString();
      SHA3.Digest256 sha3engine = new SHA3.Digest256();
      byte[] digest = sha3engine.digest(text.getBytes());
      String digestString = Hex.toHexString(digest);
      return digestString;
    }
}

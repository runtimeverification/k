// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.bouncycastle.jcajce.provider.digest.SHA3;
import org.bouncycastle.util.encoders.Hex;
import org.kframework.attributes.Att;
import org.kframework.definition.Sentence;
import org.kframework.definition.RuleOrClaim;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.util.Optional;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class NumberSentences {

    public static Sentence number(Sentence s) {
        if (!(s instanceof RuleOrClaim)) {
            return s;
        }
        String id = ruleHash(s.withAtt(Att.empty()));
        return s.withAtt(s.att().add("UNIQUE_ID", id));
    }

    private static String ruleHash(Sentence s) {
        String text = new NormalizeVariables().normalize(s).toString();
        SHA3.Digest256 sha3engine = new SHA3.Digest256();
        byte[] digest = sha3engine.digest(text.getBytes());
        String digestString = Hex.toHexString(digest);
        return digestString;
    }
}

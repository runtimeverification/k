// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.bouncycastle.jcajce.provider.digest.SHA3;
import org.bouncycastle.util.encoders.Hex;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class NumberSentences implements AutoCloseable {

    private final FileUtil files;
    private final PrintWriter allRulesFile;

    public NumberSentences(FileUtil files) {
        this.files = files;
        files.resolveKompiled(".").mkdirs();
        try {
            allRulesFile = new PrintWriter(new BufferedWriter(new FileWriter(files.resolveKompiled("allRules.txt").getAbsolutePath())));
        } catch (IOException e) {
            throw KEMException.internalError("Could not write list of rules to coverage document.", e);
        }
    }

    public Sentence number(Sentence s) {
        String id = ruleHash(s.withAtt(Att.empty()));
        String file = s.att().get(Source.class).source();
        int line = s.att().get(Location.class).startLine();
        int col = s.att().get(Location.class).startColumn();
        String loc = file + ":" + line + ":" + col;
        allRulesFile.print(id);
        allRulesFile.print(" ");
        allRulesFile.println(loc);
        return s.withAtt(s.att().add("UNIQUE_ID", id));
    }

    private String ruleHash(Sentence s) {
        String text = new NormalizeVariables().normalize(s).toString();
        SHA3.Digest256 sha3engine = new SHA3.Digest256();
        byte[] digest = sha3engine.digest(text.getBytes());
        String digestString = Hex.toHexString(digest);
        return digestString;
    }

    @Override
    public void close() {
      allRulesFile.close();
    }
}

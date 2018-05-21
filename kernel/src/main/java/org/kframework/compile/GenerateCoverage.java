// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.compile.RewriteToTop;
import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import static org.kframework.kore.KORE.*;

public class GenerateCoverage implements AutoCloseable {
    private final boolean cover;
    private final FileUtil files;
    private final PrintWriter allRulesFile;

    public GenerateCoverage(boolean cover, FileUtil files) {
        this.cover = cover;
        this.files = files;
        files.resolveKompiled(".").mkdirs();
        try {
            allRulesFile = new PrintWriter(new BufferedWriter(new FileWriter(files.resolveKompiled("allRules.txt").getAbsolutePath())));
        } catch (IOException e) {
            throw KEMException.internalError("Could not write list of rules to coverage document.", e);
        }
    }

    public K gen(Rule r, K body) {
        if (!cover || !r.att().getOptional(Source.class).isPresent()) {
            return body;
        }
        K left = RewriteToTop.toLeft(body);
        K right = RewriteToTop.toRight(body);
        String file = r.att().get(Source.class).source();
        if (file.startsWith(JarInfo.getKBase())) {
            return body;
        }
        int line = r.att().get(Location.class).startLine();
        int col = r.att().get(Location.class).startColumn();
        String loc = file + ":" + line + ":" + col;
        String id = r.att().get("UNIQUE_ID");
        allRulesFile.print(id);
        allRulesFile.print(" ");
        allRulesFile.println(loc);
        if (r.att().contains("macro")) {
            //handled by macro expander
            return body;
        }
        return KRewrite(left, KSequence(KApply(KLabel("#logToFile"),
            KToken(StringUtil.enquoteKString(files.resolveKompiled("coverage.txt").getAbsolutePath()), Sorts.String()),
            KToken(StringUtil.enquoteKString(id + '\n'), Sorts.String())), right));
    }

    @Override
    public void close() {
      allRulesFile.close();
    }
}

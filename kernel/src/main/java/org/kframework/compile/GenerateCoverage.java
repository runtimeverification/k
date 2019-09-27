// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.compile.RewriteToTop;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.utils.StringUtil;
import org.kframework.utils.file.FileUtil;

import static org.kframework.kore.KORE.*;

public class GenerateCoverage {
    private final boolean cover;
    private final FileUtil files;

    public GenerateCoverage(boolean cover, FileUtil files) {
        this.cover = cover;
        this.files = files;
    }

    public K gen(Rule r, K body, Module mod) {
        if (!cover || !r.att().getOptional(Source.class).isPresent()) {
            return body;
        }
        K left = RewriteToTop.toLeft(body);
        K right = RewriteToTop.toRight(body);
        String id = r.att().get("UNIQUE_ID");

        if (ExpandMacros.isMacro(r)) {
            //handled by macro expander
            return body;
        }

        AddSortInjections inj = new AddSortInjections(mod);

        Sort s = inj.sort(right, Sorts.K());

        K k = KSequence(KApply(KLabel("#logToFile"),
            KToken(StringUtil.enquoteKString(files.resolveKompiled("coverage.txt").getAbsolutePath()), Sorts.String()),
            KToken(StringUtil.enquoteKString(id + '\n'), Sorts.String())), right);

        if (!s.equals(Sorts.K())) {
            k = KApply(KLabel("project:" + s.toString()), k);
        }

        return KRewrite(left, k);
    }
}

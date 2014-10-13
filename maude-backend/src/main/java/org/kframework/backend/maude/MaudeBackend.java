// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.maude;

import org.kframework.compile.sharing.FreshVariableNormalizer;
import org.kframework.compile.sharing.SortRulesNormalizer;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringBuilderUtil;
import org.kframework.utils.file.FileUtil;

public class MaudeBackend {

    private final Stopwatch sw;
    private final Context context;
    private final FileUtil files;
    public MaudeBackend(Stopwatch sw, Context context, FileUtil files) {
        this.sw = sw;
        this.context = context;
        this.files = files;
    }

    public void run(Definition definition) {
        definition = (Definition) new FreshVariableNormalizer(context).visitNode(definition);
        definition = (Definition) new SortRulesNormalizer(context).visitNode(definition);
        MaudeFilter maudeFilter = new MaudeFilter(context);
        maudeFilter.visitNode(definition);

        final String mainModule = definition.getMainModule();
        StringBuilder maudified = maudeFilter.getResult();
        StringBuilderUtil.replaceFirst(maudified, mainModule, mainModule + "-BASE");

        files.saveToKompiled("base.maude", maudified.toString());
        sw.printIntermediate("Generating Maude file");
    }
}

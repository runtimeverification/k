// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.maude;

import org.kframework.backend.BasicBackend;
import org.kframework.compile.transformers.DeleteFunctionRules;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import com.google.inject.Inject;

import java.io.IOException;
import java.util.Properties;

public class KompileBackend extends BasicBackend {

    private final FileUtil files;

    @Inject
    KompileBackend(Stopwatch sw, Context context, FileUtil files) {
        super(sw, context);
        this.files = files;
    }

    @Override
    public Definition firstStep(Definition javaDef) {
        Properties specialMaudeHooks = new Properties();
        Properties maudeHooks = new Properties();
        try {
            FileUtil.loadProperties(maudeHooks, getClass(), "MaudeHooksMap.properties");
            FileUtil.loadProperties(specialMaudeHooks, getClass(), "SpecialMaudeHooks.properties");
        } catch (IOException e) {
            e.printStackTrace();
        }
        MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(maudeHooks, specialMaudeHooks, context);
        builtinsFilter.visitNode(javaDef);
        final String mainModule = javaDef.getMainModule();
        StringBuilder builtins = new StringBuilder()
            .append("mod ").append(mainModule).append("-BUILTINS is\n").append(" including ")
            .append(mainModule).append("-BASE .\n")
            .append(builtinsFilter.getResult()).append("endm\n");

        files.saveToKompiled("builtins.maude", builtins.toString());
        sw.printIntermediate("Generating equations for hooks");
        javaDef = (Definition) new DeleteFunctionRules(maudeHooks.stringPropertyNames(), context)
            .visitNode(javaDef);
        return super.firstStep(javaDef);
    }

    @Override
    public void run(Definition javaDef) {
        MaudeBackend maude = new MaudeBackend(sw, context, files);
        maude.run(javaDef);

        String load = "load \"" + JarInfo.getKBase(true) + JarInfo.MAUDE_LIB_DIR + "/k-prelude\"\n";

        final String mainModule = javaDef.getMainModule();
        //String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$", "");

        StringBuilder main = new StringBuilder().append(load).append("load \"base.maude\"\n")
            .append("load \"builtins.maude\"\n").append("mod ").append(mainModule).append(" is \n")
            .append("  including ").append(mainModule).append("-BASE .\n")
            .append("  including ").append(mainModule).append("-BUILTINS .\n")
            .append("eq mainModule = '").append(mainModule).append(" .\nendm\n");
        files.saveToKompiled("main.maude", main.toString());
    }

    @Override
    public String getDefaultStep() {
        return "LastStep";
    }

    @Override
    public boolean documentation() {
        return false;
    }

    @Override
    public boolean generatesDefinition() {
        return true;
    }

}

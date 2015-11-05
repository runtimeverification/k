// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.coq;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backends;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.OS;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;

public class CoqBackend {

    private final FileUtil files;
    private final Provider<ProcessBuilder> pb;
    private final Context context;
    private final KompileOptions options;

    @Inject
    public CoqBackend(Stopwatch sw, Context context, KompileOptions options, Provider<ProcessBuilder> pb, FileUtil files) {
        this.context = context;
        this.options = options;
        this.pb = pb;
        this.files = files;
    }

    public void run(Definition definition) {
        final String labelFile = FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + ".labeled_rules";
        final String langName = definition.getMainModule().toLowerCase();
        final String domainFile = langName+"_domains.v";
        final String ruleFile = langName+"_rules.v";

        CoqLabelUnparser unparser = new CoqLabelUnparser(context);
        unparser.visitNode(definition);
        String unparsedText = unparser.getResult();

        files.saveToDefinitionDirectory(labelFile, unparsedText);

        final String kcoq = OS.current().getNativeExecutable("kcoq");
        File directory = definition.getMainFile().getParentFile();

        try {
            Process p = pb.get().command(kcoq,"syntax","--recursive",
                    definition.getMainFile().getAbsolutePath(),domainFile)
              .inheritIO().directory(directory).start();
            int result;
            try {
                result = p.waitFor();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                p.destroy();
                return;
            }
            if (result != 0) {
                throw KEMException.criticalError("Error generating Coq syntax definition");
            }
        } catch (IOException e) {
            throw KEMException.criticalError("Error generating Coq syntax definition", e);
        }
        try {
            Process p = pb.get().command(kcoq,"rules","--lang-name",langName,"--recursive",
                    definition.getMainFile().getAbsolutePath(),"--rules-from",labelFile,ruleFile)
              .inheritIO().directory(directory).start();
            int result;
            try {
                result = p.waitFor();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                p.destroy();
                return;
            }
            if (result != 0) {
                throw KEMException.criticalError("Error generating Coq rules definition");
            }
        } catch (IOException e) {
            throw KEMException.criticalError("Error generating Coq rules definition", e);
        }
    }

    public String getDefaultStep() {
        return "LastStep";
    }

    public String autoincludedFile() {
        return Backends.AUTOINCLUDE_JAVA;
    }
    public boolean generatesDefinition() {
        return false;
    }
}

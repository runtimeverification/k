// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.coq;

import java.io.File;
import java.io.IOException;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backends;
import org.kframework.backend.BasicBackend;
import org.kframework.backend.FirstStep;
import org.kframework.backend.LastStep;
import org.kframework.compile.transformers.AddHeatingConditions;
import org.kframework.compile.transformers.ContextsToHeating;
import org.kframework.compile.transformers.StrictnessToContexts;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.OS;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class CoqBackend extends BasicBackend {
    private final KExceptionManager kem;

    @Inject
    public CoqBackend(Stopwatch sw, Context context, KExceptionManager kem) {
        super(sw, context);
        this.kem = kem;
    }

    @Override
    public void run(Definition definition) {
        final String labelFile = FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + ".labeled_rules";
        final String langName = definition.getMainModule().toLowerCase();
        final String domainFile = langName+"_domains.v";
        final String ruleFile = langName+"_rules.v";

        CoqLabelUnparser unparser = new CoqLabelUnparser(context);
        unparser.visitNode(definition);
        String unparsedText = unparser.getResult();

        FileUtil.save(options.directory.getPath() + File.separator + labelFile, unparsedText);

        final File kcoqFile = OS.current().getNativeExecutable("kcoq");
        final String kcoq = kcoqFile.getAbsolutePath();
        if (!kcoqFile.canExecute()) {
            kem.registerCriticalError("Could not find kcoq exectuable for your platform, check that it is installed at "
              +kcoq+" and is executable.");
            return;
        }
        File directory = new File(definition.getMainFile()).getParentFile();

        try {
            Process p = new ProcessBuilder(kcoq,"syntax","--recursive",
                    definition.getMainFile(),domainFile)
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
                kem.registerCriticalError("Error generating Coq syntax definition");
                return;
            }
        } catch (IOException e) {
            kem.registerCriticalError("Error generating Coq syntax definition", e);
        }
        try {
            Process p = new ProcessBuilder(kcoq,"rules","--lang-name",langName,"--recursive",
                    definition.getMainFile(),"--rules-from",labelFile,ruleFile)
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
                kem.registerCriticalError("Error generating Coq rules definition");
                return;
            }
        } catch (IOException e) {
            kem.registerCriticalError("Error generating Coq rules definition", e);
        }
    }


    @Override
    public String getDefaultStep() {
        return "LastStep";
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        CompilerSteps<Definition> steps = new CompilerSteps<Definition>(context);
        steps.add(new FirstStep(this, context));
        steps.add(new StrictnessToContexts(context));
        steps.add(new ContextsToHeating(context));
        steps.add(new AddHeatingConditions(context));
        steps.add(new LastStep(this, context));
        return steps;
    }

    @Override
    public String autoincludedFile() {
        return Backends.AUTOINCLUDE_JAVA;
    }

    @Override
    public boolean documentation() {
        return false;
    }

    @Override
    public boolean generatesDefinition() {
        return false;
    }
}

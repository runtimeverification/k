// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;

/**
 * Created by dwightguth on 8/25/15.
 */
public class OcamlCompileExecutionMode implements ExecutionMode<Void> {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final OcamlKRunOptions ocamlOptions;
    private final DefinitionToOcaml converter;
    private final KRunOptions options;

    @Inject
    public OcamlCompileExecutionMode(
            KExceptionManager kem,
            FileUtil files,
            GlobalOptions globalOptions,
            KompileOptions kompileOptions,
            CompiledDefinition def,
            OcamlRewriter.InitializeDefinition init,
            KRunOptions options,
            OcamlKRunOptions ocamlOptions) {
        this.kem = kem;
        this.files = files;
        this.ocamlOptions = ocamlOptions;
        this.converter = new DefinitionToOcaml(kem, files, globalOptions, kompileOptions, null);
        converter.initialize(init.serialized, def);
        this.options = options;
    }

    @Override
    public Void execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        if (options.exitCodePattern != null) {
            Rule pattern = KRun.pattern(files, kem, options.exitCodePattern, options, compiledDefinition, Source.apply("<command line: --exit-code>"));

            String ocaml = converter.ocamlCompile(k, pattern, ocamlOptions.dumpExitCode);
            files.saveToTemp("pgm.ml", ocaml);
            try {
                new OcamlRewriter(files, converter, options).compileOcaml("pgm.ml");
                String outputFile = options.outputFile;
                if (outputFile == null) {
                    outputFile = "a.out";
                }
                FileUtils.copyFile(files.resolveTemp("a.out"), files.resolveWorkingDirectory(outputFile));
                return null;
            } catch (IOException e) {
                throw KEMException.criticalError("Failed to start ocamlopt: " + e.getMessage(), e);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                throw KEMException.criticalError("Ocaml process interrupted.", e);
            }
        } else {
            throw KEMException.criticalError("Cannot compile a native binary without an --exit-code flag.");
        }
    }
}

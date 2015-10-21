// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.kframework.kore.ToKast;
import org.kframework.rewriter.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.kframework.kore.KORE.*;

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
            Rule pattern = KRun.compilePattern(files, kem, options.exitCodePattern, options, compiledDefinition, Source.apply("<command line: --exit-code>"));

            Map<String, String> serializedVars = new HashMap<>();
            List<K> unserializedVars = new ArrayList<>();
            if (!ocamlOptions.serializeConfig.isEmpty()) {
                if (k instanceof KApply) {
                    KApply kapp = (KApply)k;
                    if (kapp.klabel().equals(compiledDefinition.topCellInitializer)) {
                        if (kapp.klist().size() == 1) {
                            List<K> elements = Assoc.flatten(KLabel("_Map_"), kapp.klist().items(), KLabel(".Map"));
                            for (K element : elements) {
                                if (element instanceof KApply) {
                                    KApply elementKApp = (KApply) element;
                                    if (elementKApp.klabel().equals(KLabel("_|->_")) && elementKApp.klist().size() == 2) {
                                        K key = elementKApp.klist().items().get(0);
                                        K value = elementKApp.klist().items().get(1);
                                        if (key instanceof KToken) {
                                            KToken configVar = (KToken) key;
                                            if (configVar.sort().equals(Sorts.KConfigVar()) && ocamlOptions.serializeConfig.contains(configVar.s())) {
                                                serializedVars.put(configVar.s(), marshalValue(value));
                                                continue;
                                            }
                                        }
                                    }
                                }
                                unserializedVars.add(element);
                            }
                        }
                    }
                }
            }

            String ocaml;
            if (!unserializedVars.isEmpty() && !serializedVars.isEmpty()) {
                k = unserializedVars.stream().reduce(KApply(KLabel(".Map")), (k1, k2) -> (KApply(KLabel("_Map_"), k1, k2)));
                ocaml = converter.ocamlCompile(k, serializedVars, compiledDefinition.topCellInitializer, pattern, ocamlOptions.dumpExitCode);
            } else {
                ocaml = converter.ocamlCompile(k, pattern, ocamlOptions.dumpExitCode);
            }

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

    /**
     * Marshals the specified K term using the OCAML Marshal module and returns a string containing the ocaml representation of a string of the resulting bytes.
     * @param value
     * @return
     */
    private String marshalValue(K value) {
        files.saveToTemp("run.in", ToKast.apply(converter.preprocess(value)));
        try {
            int exit = files.getProcessBuilder().command(files.resolveKompiled("marshalvalue").getAbsolutePath()).directory(files.resolveTemp(".")).start().waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("Failed to precompile program variables.");
            }
            return FileUtils.readFileToString(files.resolveTemp("run.out"));
        }catch (IOException e) {
            throw KEMException.criticalError("Failed to start ocamlopt: " + e.getMessage(), e);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw KEMException.criticalError("Ocaml process interrupted.", e);
        }
    }
}

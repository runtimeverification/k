// Copyright (c) 2015-2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.apache.commons.io.IOUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
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
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.ToBinary;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 8/25/15.
 */
public class OcamlCompileExecutionMode implements ExecutionMode {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final OcamlKRunOptions ocamlKRunOptions;
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
            OcamlKRunOptions ocamlKRunOptions) {
        this.kem = kem;
        this.files = files;
        this.ocamlKRunOptions = ocamlKRunOptions;
        this.converter = new DefinitionToOcaml(kem, files, globalOptions, kompileOptions, null);
        converter.initialize(init.serialized, def);
        this.options = options;
    }

    @Override
    public Tuple2<K, Integer> execute(KRun.InitialConfiguration k, Function<Module, Rewriter> ignored, CompiledDefinition compiledDefinition) {
        if (compiledDefinition.exitCodePattern != null) {
            // serializedVars will not be evaluated at program load.
            // This is faster, but their definition may not include impure functions
            final List<String> serializeVarNames = converter.options.serializeConfig;
            K serializedVars = KApply(KLabel(".Map"));
            // The unserializedVars will be reevaluated each time the kcc-compiled program
            // is executed, so they can for example call #argv() to read command-line arguments.
            List<K> unserializedVars = new ArrayList<>();
            K unserializedVarsMap;
            if (!serializeVarNames.isEmpty()) {
                if (k.theConfig instanceof KApply) {
                    KApply kapp = (KApply)k.theConfig;
                    k.theConfig = null;
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
                                            if (configVar.sort().equals(Sorts.KConfigVar()) && serializeVarNames.contains(configVar.s())) {
                                                serializedVars = KApply(KLabel("_Map_"),element,serializedVars);
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
                unserializedVarsMap = unserializedVars.stream().reduce(KApply(KLabel(".Map")), (k1, k2) -> (KApply(KLabel("_Map_"), k1, k2)));
            } else {
                unserializedVarsMap = k.theConfig;
                k.theConfig = null;
            }

            files.saveToTemp("kore_term",ToBinary.apply(converter.preprocess(unserializedVarsMap)));
            files.saveToTemp("marshal_term", marshalValue(serializedVars));
            files.saveToTemp("plugin_path",files.resolveKompiled("realdef.cmxs").getAbsolutePath());
            try {
                OcamlRewriter rewriter = new OcamlRewriter(files, converter, options);
                rewriter.createResourceObject("kore_term");
                rewriter.createResourceObject("marshal_term");
                rewriter.createResourceObject("plugin_path");
                String outputFile = options.print.outputFile;
                if (outputFile == null) {
                    outputFile = "a.out";
                }
                rewriter.linkOcamlObject(ocamlKRunOptions.nativeCompiler,
                        files.resolveKompiled("execution_partial.o").getAbsolutePath(),
                        files.resolveWorkingDirectory(outputFile).getAbsolutePath(),
                        files.resolveTemp("kore_term.o").getAbsolutePath(),
                        files.resolveTemp("marshal_term.o").getAbsolutePath(),
                        files.resolveTemp("plugin_path.o").getAbsolutePath());
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
    private byte[] marshalValue(K value) {
        files.saveToTemp("run.in", ToBinary.apply(converter.preprocess(value)));
        try {
            Process p = files.getProcessBuilder().command(files.resolveKompiled("marshalvalue").getAbsolutePath(), files.resolveKompiled("realdef.cma").getAbsolutePath()).directory(files.resolveTemp(".")).start();
            int exit = p.waitFor();
            if (exit != 0) {
                IOUtils.copy(p.getErrorStream(), System.err);
                throw KEMException.criticalError("Failed to precompile program variables.");
            }
            return FileUtils.readFileToByteArray(files.resolveTemp("run.out"));
        }catch (IOException e) {
            throw KEMException.criticalError("Failed to start ocamlopt: " + e.getMessage(), e);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw KEMException.criticalError("Ocaml process interrupted.", e);
        }
    }
}

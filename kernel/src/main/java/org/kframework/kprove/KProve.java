// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kprove;

import com.google.inject.Inject;
import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.RewriterResult;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.ToJson;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.function.Function;


/**
 * Class that implements the "--prove" option.
 */
public class KProve {

    public static final String BOUNDARY_CELL_PREFIX = "BOUND_";

    private final KExceptionManager kem;
    private final FileUtil files;
    private final KPrint kprint;
    private final KProveOptions kproveOptions;
    private final GlobalOptions globalOptions;
    private final CompiledDefinition compiledDefinition;
    private final BinaryLoader loader;
    private final ProofDefinitionBuilder proofDefinitionBuilder;
    private final Function<Definition, Rewriter> rewriterGenerator;
    private final Stopwatch sw;

    @Inject
    public KProve(KExceptionManager kem, FileUtil files, KPrint kprint, KProveOptions kproveOptions,
                  GlobalOptions globalOptions, CompiledDefinition compiledDefinition, BinaryLoader loader,
                  ProofDefinitionBuilder proofDefinitionBuilder, Function<Definition, Rewriter> rewriterGenerator, Stopwatch sw) {
        this.kem = kem;
        this.files = files;
        this.kprint = kprint;
        this.kproveOptions = kproveOptions;
        this.globalOptions = globalOptions;
        this.compiledDefinition = compiledDefinition;
        this.loader = loader;
        this.proofDefinitionBuilder = proofDefinitionBuilder;
        this.rewriterGenerator = rewriterGenerator;
        this.sw = sw;
        if (kproveOptions.emitJsonSpec != null) {
            throw KEMException.criticalError("Option `--emit-json-spec` only supported in kprovex tool!");
        }
    }

    public int run() {
        if (!kproveOptions.specFile(files).exists()) {
            throw KEMException.criticalError("Definition file doesn't exist: " +
                    kproveOptions.specFile(files).getAbsolutePath());
        }

        Tuple2<Definition, Module> compiled = proofDefinitionBuilder
                .build(kproveOptions.specFile(files), kproveOptions.defModule, kproveOptions.specModule, compiledDefinition.kompileOptions.readOnlyKompiledDirectory);

        if (kproveOptions.saveProofDefinitionTo != null) {
            saveFullDefinition(compiled._1());
        }

        Rewriter rewriter = rewriterGenerator.apply(compiled._1());
        Module specModule = compiled._2();

        if (kproveOptions.emitJson) {
            try {
                files.saveToKompiled("prove-definition.json", new String(ToJson.apply(compiled._1()), "UTF-8"));
            } catch (UnsupportedEncodingException e) {
                throw KEMException.criticalError("Unsupported encoding `UTF-8` when saving JSON definition.");
            }
        }

        RewriterResult results = rewriter.prove(specModule, false);
        sw.printIntermediate("Backend");
        kprint.prettyPrint(compiled._1(), compiled._1().getModule("LANGUAGE-PARSING").get(), kprint::outputFile,
                results.k());
        sw.printTotal("Total");
        return results.exitCode().orElse(KEMException.TERMINATED_WITH_ERRORS_EXIT_CODE);
    }

    // Saving combined verification definition to disk to be usable by other tools (e.g., kast)
    private void saveFullDefinition(Definition fullDefinition) {
        CompiledDefinition fullCompiledDefinition = new CompiledDefinition(
                compiledDefinition.kompileOptions, kproveOptions.outerParsing,
                kproveOptions.innerParsing, globalOptions,
                fullDefinition, fullDefinition,
                files, kem, compiledDefinition.topCellInitializer);
        Path proveKompiledDir = Paths.get(kproveOptions.saveProofDefinitionTo).resolve("prove-spec-kompiled");
        try {
            Files.createDirectories(proveKompiledDir);
            loader.saveOrDie(proveKompiledDir.resolve("compiled.bin").toFile(), fullCompiledDefinition);
        } catch (IOException e) {
            throw KEMException.criticalError(
                    "Could not create proof output directory " + proveKompiledDir.toAbsolutePath(), e);
        }
    }
}

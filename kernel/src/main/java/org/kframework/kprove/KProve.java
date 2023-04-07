// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kprove;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.ToJson;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.io.UnsupportedEncodingException;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;

public class KProve {

    public static final String BOUNDARY_CELL_PREFIX = "BOUND_";

    private static final int KPROVE_SUCCESS_EXIT_CODE = 0;
    private static final int KPROVE_MISMATCH_CONFIG_CODE = 1;

    private final KExceptionManager kem;
    private final FileUtil files;
    private final KPrint kprint;
    private final KProveOptions kproveOptions;
    private final CompiledDefinition compiledDefinition;
    private final BinaryLoader loader;
    private final ProofDefinitionBuilder proofDefinitionBuilder;
    private final Function<Definition, Rewriter> rewriterGenerator;
    private final Stopwatch sw;

    @Inject
    public KProve(KExceptionManager kem, FileUtil files, KPrint kprint, KProveOptions kproveOptions,
                  CompiledDefinition compiledDefinition, BinaryLoader loader,
                  ProofDefinitionBuilder proofDefinitionBuilder, Function<Definition, Rewriter> rewriterGenerator, Stopwatch sw) {
        this.kem = kem;
        this.files = files;
        this.kprint = kprint;
        this.kproveOptions = kproveOptions;
        this.compiledDefinition = compiledDefinition;
        this.loader = loader;
        this.proofDefinitionBuilder = proofDefinitionBuilder;
        this.rewriterGenerator = rewriterGenerator;
        this.sw = sw;
        // validate kprovex options. There are too many dependencies to have duplicate options files
        // so use the same class, but throw an error if used by accident. It would have been silent anyway.
        // TODO: remove once transition to kprovex is finished
        if (kproveOptions.defModule != null) {
            throw KEMException.criticalError("Option `--def-module` no longer supported in the kprovex tool.");
        }
        if (kproveOptions.saveProofDefinitionTo != null) {
            throw KEMException.criticalError("Option `--save-proof-definition-to` no longer supported in the kprovex tool.");
        }
        if (!kproveOptions.extraConcreteRuleLabels.isEmpty()) {
            throw KEMException.criticalError("Option `--concrete-rules` no longer supported in the kprovex tool.");
        }
    }

    public int run() {
        if (!kproveOptions.specFile(files).exists()) {
            throw KEMException.criticalError("Definition file doesn't exist: " +
                    kproveOptions.specFile(files).getAbsolutePath());
        }

        Tuple2<Definition, Module> compiled = proofDefinitionBuilder
                .build(kproveOptions.specFile(files), kproveOptions.specModule, compiledDefinition.kompileOptions.readOnlyKompiledDirectory);

        Rewriter rewriter = rewriterGenerator.apply(compiled._1());
        Module specModule = compiled._2();

        if (kproveOptions.emitJson) {
            try {
                files.saveToKompiled("prove-definition.json", new String(ToJson.apply(compiled._1()), "UTF-8"));
            } catch (UnsupportedEncodingException e) {
                throw KEMException.criticalError("Unsupported encoding `UTF-8` when saving JSON definition.");
            }
        }

        if (kproveOptions.emitJsonSpec != null) {
            Set<String> names = stream(compiled._1().modules()).map(Module::name).collect(Collectors.toSet());
            Set<Module> specMods = stream(specModule.importedModules()).filter(m -> !names.contains(m.name())).collect(Collectors.toSet());
            specMods.add(specModule);
            files.saveToWorkingDirectory(kproveOptions.emitJsonSpec, ToJson.apply(specMods, specModule.name()));
        }

        RewriterResult results = rewriter.prove(specModule, true);
        sw.printIntermediate("Backend");
        kprint.prettyPrint(compiled._1(), compiled._1().getModule("LANGUAGE-PARSING").get(), kprint::outputFile,
                results.k());
        sw.printTotal("Total");

        int errCode = results.exitCode().orElse(0);
        switch (errCode) {
        case KPROVE_SUCCESS_EXIT_CODE:
            break;
        case KPROVE_MISMATCH_CONFIG_CODE:
            kem.addKException( new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.PROVER,
                    "backend terminated because the configuration cannot be rewritten further. See output for more details."));
            break;
        default:
            kem.addKException( new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.PROVER,
                    "backend crashed with exit code " + String.valueOf(errCode)));
            break;
        }

        return results.exitCode().orElse(KEMException.TERMINATED_WITH_ERRORS_EXIT_CODE);
    }
}

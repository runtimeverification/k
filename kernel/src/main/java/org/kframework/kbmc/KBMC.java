// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kbmc;

import org.kframework.RewriterResult;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kprove.ProofDefinitionBuilder;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import javax.inject.Inject;
import java.util.function.Function;

public class KBMC {
    private final ProofDefinitionBuilder proofDefinitionBuilder;
    private final FileUtil files;
    private final KPrint kprint;
    private final KBMCOptions options;
    private final Function<Definition, Rewriter> rewriterGenerator;

    @Inject
    public KBMC(ProofDefinitionBuilder proofDefinitionBuilder, FileUtil files, KPrint kprint, KBMCOptions options,
                Function<Definition, Rewriter> rewriterGenerator) {
        this.proofDefinitionBuilder = proofDefinitionBuilder;
        this.files = files;
        this.kprint = kprint;
        this.options = options;
        this.rewriterGenerator = rewriterGenerator;
    }

    public int run() {
        if (!options.specFile(files).exists()) {
            throw KEMException.criticalError("Definition file doesn't exist: " +
                    options.specFile(files).getAbsolutePath());
        }

        Tuple2<CompiledDefinition, Module> compiled = proofDefinitionBuilder
                .build(options.specFile(files), options.defModule, options.specModule);
        Rewriter rewriter = rewriterGenerator.apply(compiled._1().kompiledDefinition);
        Module specModule = compiled._2();

        RewriterResult results = rewriter.bmc(specModule);
        kprint.prettyPrint(compiled._1().kompiledDefinition, compiled._1().kompiledDefinition.getModule("LANGUAGE-PARSING").get(), kprint::outputFile,
                results.k());
        return results.exitCode().orElse(KEMException.TERMINATED_WITH_ERRORS_EXIT_CODE);
    }
}

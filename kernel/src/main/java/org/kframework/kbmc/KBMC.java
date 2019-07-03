// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kbmc;

import org.kframework.RewriterResult;
import org.kframework.compile.Backend;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kprove.KProve;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.util.function.Function;

public class KBMC {
    private final KExceptionManager kem;
    private final Stopwatch sw;
    private final FileUtil files;
    private final KPrint kprint;

    public KBMC(KExceptionManager kem, Stopwatch sw, FileUtil files, KPrint kprint) {
        this.kem    = kem;
        this.sw     = sw;
        this.files  = files;
        this.kprint = kprint;
    }

    public int run(KBMCOptions options, CompiledDefinition compiledDefinition, Backend backend, Function<Definition, Rewriter> rewriterGenerator) {
        Tuple2<Definition, Module> compiled = KProve.getProofDefinition(options.specFile(files),
                options.defModule, options.specModule, compiledDefinition, backend, files, kem, sw);
        Rewriter rewriter = rewriterGenerator.apply(compiled._1());
        Module specModule = compiled._2();

        RewriterResult results = rewriter.bmc(specModule);
        kprint.prettyPrint(compiled._1(), compiled._1().getModule("LANGUAGE-PARSING").get(), s -> kprint.outputFile(s), results.k());
        return results.exitCode().orElse(KEMException.TERMINATED_WITH_ERRORS_EXIT_CODE);
    }
}

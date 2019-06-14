package org.kframework.kbmc;

import org.kframework.compile.Backend;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kprove.KProve;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.utils.Stopwatch;
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

        K results = rewriter.bmc(specModule);
        int exit;
        if (results instanceof KApply) {
            KApply kapp = (KApply) results;
            exit = kapp.klabel().name().equals("#True") ? 0 : 1;
        } else {
            exit = 1;
        }
        kprint.prettyPrint(compiled._1(), compiled._1().getModule("LANGUAGE-PARSING").get(), s -> kprint.outputFile(s), results);
        return exit;
    }
}

// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kil.Attributes;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.parser.ProductionReference;
import org.kframework.transformation.Transformation;
import org.kframework.unparser.AddBrackets;
import org.kframework.unparser.KOREToTreeNodes;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.function.Function;

/**
 * The KORE-based KRun
 */
public class KRun implements Transformation<Void, Void> {

    private final KExceptionManager kem;
    private final FileUtil files;

    public KRun(KExceptionManager kem, FileUtil files) {
        this.kem = kem;
        this.files = files;
    }

    public int run(CompiledDefinition compiledDef, KRunOptions options, Function<Module, Rewriter> rewriterGenerator) {
        String pgmFileName = options.configurationCreation.pgm();
        if (!options.configurationCreation.term()) {
            throw KEMException.criticalError("Unsupported options: term=false");
        }

        String pgm = files.loadFromWorkingDirectory(pgmFileName);
        K program = compiledDef.getProgramParser().apply(pgm, Source.apply(pgm));

        Rewriter rewriter = rewriterGenerator.apply(compiledDef.executionModule());

        K result = rewriter.execute(program);

        System.err.println(unparseTerm(result, compiledDef.kompiledDefinition.mainSyntaxModule()));
        return 0;
    }

    private String unparseTerm(K input, Module test) {
        return KOREToTreeNodes.toString(
                new AddBrackets(test).addBrackets((ProductionReference)
                        KOREToTreeNodes.apply(KOREToTreeNodes.up(input), test)));
    }

    @Override
    public Void run(Void aVoid, Attributes attrs) {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }
}

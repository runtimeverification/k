package org.kframework.keq;

import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.function.Function;

public class KEq {
    public KEq(KExceptionManager kem, FileUtil files) {
    }

    public int run(
            CompiledDefinition commonDef,
            CompiledDefinition def1,
            CompiledDefinition def2,
            KEqOptions keqOptions,
            Function<Module, Rewriter> commonGen,
            Function<Module, Rewriter> gen1,
            Function<Module, Rewriter> gen2) {
        Rewriter commonRewriter = commonGen.apply(commonDef.executionModule());
        Rewriter rewriter1 = gen1.apply(def1.executionModule());
        Rewriter rewriter2 = gen2.apply(def2.executionModule());

        boolean isEquivalent = commonRewriter.equivalence(rewriter1, rewriter2, keqOptions.spec1, keqOptions.spec2);
        System.out.println(isEquivalent);
        return isEquivalent ? 0 : 1;
    }
}

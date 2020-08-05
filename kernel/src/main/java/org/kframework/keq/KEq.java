// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.keq;

import com.google.inject.Inject;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kprove.ProofDefinitionBuilder;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.util.function.Function;

public class KEq {
    private final KEqOptions keqOptions;

    @Inject
    public KEq(KEqOptions keqOptions) {
        this.keqOptions = keqOptions;
    }

    public int run(CompiledDefinition commonDef, Function<Definition, Rewriter> commonGen,
                   Function<Definition, Rewriter> gen1,
                   Function<Definition, Rewriter> gen2,
                   ProofDefinitionBuilder pdb1,
                   ProofDefinitionBuilder pdb2,
                   FileUtil files) {
        Rewriter commonRewriter = commonGen.apply(commonDef.kompiledDefinition);

        Tuple2<Definition, Module> compiled1 = pdb1.build(
                files.resolveWorkingDirectory(keqOptions.spec1), keqOptions.defModule1, keqOptions.specModule1);
        Rewriter rewriter1 = gen1.apply(compiled1._1());
        Module spec1 = compiled1._2();

        Tuple2<Definition, Module> compiled2 = pdb2.build(
                files.resolveWorkingDirectory(keqOptions.spec2), keqOptions.defModule2, keqOptions.specModule2);
        Rewriter rewriter2 = gen2.apply(compiled2._1());
        Module spec2 = compiled2._2();

        boolean isEquivalent = commonRewriter.equivalence(rewriter1, rewriter2, spec1, spec2);
        System.out.println(isEquivalent ? "#Top" : "#Bottom");
        return isEquivalent ? 0 : 1;
    }
}

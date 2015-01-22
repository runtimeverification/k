// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.compile;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kore.convertors.KILtoKORE;
import org.kframework.kore.convertors.KOREtoKIL;

public class KORECompilationSteps extends BasicCompilerStep<Definition> {

    public KORECompilationSteps(Context context) {
        super(context);
    }

    @Override
    public Definition compile(Definition ast, String haltAfterStep) throws CompilerStepDone {
//        KILtoKORE kilToKORE = new KILtoKORE(context);
//        KOREtoKIL koreToKIL = new KOREtoKIL();

//        org.kframework.kore.outer.Definition koreDefinition = kilToKORE.apply(ast);
//        Definition newKIL = koreToKIL.convertDefinition(koreDefinition);

        return ast;
    }

    @Override
    public String getName() {
        return "KORE-based Compilation Steps";
    }
}

// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.backend.java.compile;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;

public class KORECompilationSteps extends BasicCompilerStep<Definition> {

    public KORECompilationSteps(Context context) {
        super(context);
    }

    @Override
    public Definition compile(Definition ast, String haltAfterStep) throws CompilerStepDone {
        return ast;
    }

    @Override
    public String getName() {
        return "KORE-based Compilation Steps";
    }
}

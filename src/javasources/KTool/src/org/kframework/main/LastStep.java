// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import org.kframework.backend.Backend;
import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;

public class LastStep extends BasicCompilerStep<Definition> {
    private final Backend backend;

    public LastStep(Backend backend, Context context) {
        super(context);
        this.backend = backend;
    }

    @Override
    public Definition compile(Definition def, String stepName)
            throws CompilerStepDone {
        return backend.lastStep(def);
    }

    @Override
    public String getName() {
        return "LastStep";
    }

    @Override
    public void setSw(Stopwatch sw) {
        // TODO Auto-generated method stub

    }
}

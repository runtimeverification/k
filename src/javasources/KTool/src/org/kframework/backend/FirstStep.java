// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;

/**
 * Represents the first compilation step for the definition in a certain
 * backend.
 */
public class FirstStep extends BasicCompilerStep<Definition> {
    Backend backend;

    /**
     * @param backend
     *            the backend which contains this compilation step
     * @param context
     *            the context
     */
    public FirstStep(Backend backend, Context context) {
        super(context);
        this.backend = backend;
    }

    @Override
    public Definition compile(Definition def, String stepName)
            throws CompilerStepDone {
        return backend.firstStep(def);
    }

    @Override
    public String getName() {
        return "FirstStep";
    }
}

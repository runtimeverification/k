// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend;

import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;

import java.io.IOException;

public interface Backend {
    public void run(Definition definition) throws IOException;

    public String getDefaultStep();

    /**
     * Applies the first compilation step of this backend to a given definition.
     * 
     * @param def
     *            the given definition
     * @return the resulting definition after this compilation step
     */
    Definition firstStep(Definition def);

    /**
     * Applies the last compilation step of this backend to a given definition.
     * 
     * @param def
     *            the given definition
     * @return the resulting definition after this compilation step
     */
    Definition lastStep(Definition def);

    public boolean autoinclude();

    /**
     * Gets all compilation steps of this backend.
     * 
     * @return a compound compilation step consisting of all the compilation
     *         steps
     */
    public CompilerSteps<Definition> getCompilationSteps();
    // TODO(YilongL): why mixing the uses of "compilation step" and
    // "compiler step"? what about a uniform name?    
}

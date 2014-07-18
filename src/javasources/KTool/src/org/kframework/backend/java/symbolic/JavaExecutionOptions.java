// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.krun.K;

import com.beust.jcommander.Parameter;


public final class JavaExecutionOptions {
    @Parameter(names="--generate-tests", description="Test programs will be generated along with "
        + "normal search.")
    public boolean generateTests = false;

    @Parameter(names="--deterministic-functions", description="Throw assertion failure during "
        + "execution in the java backend if function definitions are not deterministic.")
    public boolean deterministicFunctions = false;

    public boolean concreteExecution() {
        return K.tool() == K.Tool.KRUN && !generateTests;
    }

    public boolean fastExecution(boolean search) {
        return concreteExecution() && patternMatching && !search;
    }

    @Parameter(names="--indexing-stats", description="Measure indexing-related information.")
    public boolean indexingStats = false;

    @Parameter(names="--pattern-matching", description="Use pattern-matching rather than "
        + "unification to drive rewriting in the Java backend.")
    public boolean patternMatching = false;
}


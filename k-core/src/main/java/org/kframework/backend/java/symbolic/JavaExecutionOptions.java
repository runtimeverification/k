// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.indexing.IndexingAlgorithm;
import org.kframework.main.Tool;
import org.kframework.utils.options.BaseEnumConverter;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import com.google.inject.ProvidedBy;

public final class JavaExecutionOptions {

    public JavaExecutionOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public JavaExecutionOptions(Void v) {}

    @Parameter(names="--generate-tests", description="Test programs will be generated along with "
        + "normal search.")
    public boolean generateTests = false;

    @Parameter(names="--deterministic-functions", description="Throw assertion failure during "
        + "execution in the java backend if function definitions are not deterministic.")
    public boolean deterministicFunctions = false;

    public boolean concreteExecution() {
        return Tool.instance() == Tool.KRUN && !generateTests;
    }

    public boolean fastExecution(boolean search) {
        return concreteExecution() && patternMatching && !search;
    }

    @Parameter(names="--indexing-stats", description="Measure indexing-related information.")
    public boolean indexingStats = false;

    @Parameter(names="--pattern-matching", description="Use pattern-matching rather than "
        + "unification to drive rewriting in the Java backend.")
    public boolean patternMatching = false;

    @Parameter(names="--rule-index", converter=RuleIndexConveter.class, description="Choose a technique for indexing the rules. <rule-index> is one of [table|path]. (Default: table). This only has effect with '--backend java'.")
    public IndexingAlgorithm ruleIndex = IndexingAlgorithm.RULE_TABLE;

    public static class RuleIndexConveter extends BaseEnumConverter<IndexingAlgorithm> {

        @Override
        public Class<IndexingAlgorithm> enumClass() {
            return IndexingAlgorithm.class;
        }
    }
}


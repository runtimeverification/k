// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.indexing.IndexingAlgorithm;
import org.kframework.utils.options.BaseEnumConverter;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

public final class JavaExecutionOptions {

    public JavaExecutionOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public JavaExecutionOptions(Void v) {}

    @Parameter(names="--deterministic-functions", description="Throw assertion failure during "
        + "execution in the java backend if function definitions are not deterministic.")
    public boolean deterministicFunctions = false;

    @Parameter(names="--pattern-matching", description="Use pattern-matching rather than "
        + "unification to drive rewriting in the Java backend.")
    public boolean patternMatching = false;

    @Parameter(names="--rule-index", converter=RuleIndexConveter.class, description="Choose a technique for indexing the rules. <rule-index> is one of [table]. (Default: table). This only has effect with '--backend java'.")
    public IndexingAlgorithm ruleIndex = IndexingAlgorithm.RULE_TABLE;

    @Parameter(names="--audit-file", description="Enforce that the rule applied at the step specified by "
            + "--apply-step is a rule at the specified file and line, or fail with an error explaining why "
            + "the rule did not apply.")
    public String auditingFile;

    @Parameter(names="--audit-line", description="Enforce that the rule applied at the step specified by "
            + "--apply-step is a rule at the specified file and line, or fail with an error explaining why "
            + "the rule did not apply.")
    public Integer auditingLine;

    @Parameter(names="--audit-step", description="Enforce that the rule applied at the specified step is a rule "
            + "tagged with the value of --apply-tag, or fail with an error explaining why the rule did not apply.")
    public Integer auditingStep;

    public static class RuleIndexConveter extends BaseEnumConverter<IndexingAlgorithm> {

        public RuleIndexConveter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<IndexingAlgorithm> enumClass() {
            return IndexingAlgorithm.class;
        }
    }
}


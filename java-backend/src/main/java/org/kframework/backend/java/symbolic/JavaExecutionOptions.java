// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.beust.jcommander.Parameter;

import org.kframework.backend.java.util.StateLog;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;

import java.util.Collections;
import java.util.List;

@RequestScoped
public final class JavaExecutionOptions {

    @Parameter(names="--deterministic-functions", description="Throw assertion failure during "
        + "execution in the java backend if function definitions are not deterministic.")
    public boolean deterministicFunctions = false;

    @Parameter(names="--symbolic-execution", description="Use unification rather than "
        + "pattern matching to drive rewriting in the Java backend.")
    public boolean symbolicExecution = false;

    @Parameter(names="--audit-file", description="Enforce that the rule applied at the step specified by "
            + "--apply-step is a rule at the specified file and line, or fail with an error explaining why "
            + "the rule did not apply.")
    public String auditingFile;

    @Parameter(names="--audit-line", description="Enforce that the rule applied at the step specified by "
            + "--apply-step is a rule at the specified file and line, or fail with an error explaining why "
            + "the rule did not apply.")
    public Integer auditingLine;

    @Parameter(names="--audit-step", description="Enforce that the rule applied at the specified step is a rule "
            + "tagged with the javaBackendValue of --apply-tag, or fail with an error explaining why the rule did not apply.")
    public Integer auditingStep;

    @Parameter(names={"--state-log"}, description="Output symbolic execution debugging information")
    public boolean stateLog = false;

    @Parameter(names={"--state-log-path"}, description="Path where the debugging information should be stored")
    public String stateLogPath;

    @Parameter(names={"--state-log-id"}, description="Id of the current execution")
    public String stateLogId;

    @Parameter(names={"--state-log-events"}, converter=LogEventConverter.class, description="Comma-separated list of events to log: [OPEN|REACHINIT|REACHTARGET|REACHPROVED|NODE|RULE|SRULE|RULEATTEMPT|IMPLICATION|Z3QUERY|Z3RESULT|CLOSE]")
    public List<StateLog.LogEvent> stateLogEvents = Collections.emptyList();

    @Parameter(names="--branching-allowed", arity=1, description="Number of branching events allowed before a forcible stop.")
    public int branchingAllowed = Integer.MAX_VALUE;

    @Parameter(names="--log", description="Log every step. KEVM only.")
    public boolean log = false;

    @Parameter(names="--log-stmts-only", description="Log only steps that execute a statement, without intermediary steps. " +
            "Except when intermediary steps are important for other reason, like branching. KEVM only.")
    public boolean logStmtsOnly = false;

    @Parameter(names="--log-basic",
            description="Log most basic information: summary of initial step, final steps and final implications." +
                    " All custom logging only works for KEVM-based specs.")
    public boolean logBasic = false;

    public static class LogEventConverter extends BaseEnumConverter<StateLog.LogEvent> {

        public LogEventConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<StateLog.LogEvent> enumClass() {
            return StateLog.LogEvent.class;
        }
    }
}


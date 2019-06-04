// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.beust.jcommander.Parameter;
import org.kframework.backend.java.util.StateLog;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;

import java.util.Arrays;
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

    @Parameter(names={"--state-log-events"}, converter=LogEventConverter.class, description="Comma-separated list of events to log: [OPEN|REACHINIT|REACHTARGET|REACHPROVED|REACHUNPROVED|EXECINIT|SEARCHINIT|SEARCHREACH|NODE|RULE|SRULE|RULEATTEMPT|SRULEATTEMPT|CHECKINGCONSTRAINT|IMPLICATION|Z3QUERY|Z3RESULT|CLOSE]")
    public List<StateLog.LogEvent> stateLogEvents = Collections.emptyList();

    @Parameter(names="--cache-func", description="Cache evaluation results of pure functions. Enabled by default.", arity = 1)
    public boolean cacheFunctions = true;

    @Parameter(names="--cache-func-optimized",
            description="Clear function cache after initialization phase. Frees some memory. Use IN ADDITION to --cache-func")
    public boolean cacheFunctionsOptimized = false;

    @Parameter(names="--cache-formulas", description="Cache results of ConjunctiveFormula.simplify().")
    public boolean cacheFormulas = false;

    @Parameter(names="--cache-tostring",
            description="Cache toString() result for KItem, Equality and DisjunctiveFormula. " +
                    "Speeds up logging but eats more memory.", arity = 1)
    public boolean cacheToString = true;

    @Parameter(names="--format-failures", description="Format failure final states. By default they are printed all " +
            "on one line, using ConstrainedTerm.toString(). If option is enabled, they are printed a bit nicer, " +
            "using custom ConjunctiveFormula formatter, but still fast. Disabled by default for output compatibility " +
            "with other backends. Recommended to enable for Java backend.")
    public boolean formatFailures = false;

    @Parameter(names="--branching-allowed", arity=1, description="Number of branching events allowed before a forcible stop.")
    public int branchingAllowed = Integer.MAX_VALUE;

    @Parameter(names="--log", description="Log every step.")
    public boolean log = false;

    @Parameter(names="--log-basic",
            description="Log most basic information: summary of initial step, final steps and final implications, " +
                    "branching points.")
    public boolean logBasic = false;

    @Parameter(names="--log-cells", description="Specify what subset of configuration has to be printed when" +
            " an execution step is logged." +
            " Usage format: --log-pretty \"v2,v2,...\" , where v1,v2,... are either cell names," +
            " one of: \"#pc\", \"#initTerm\", \"#target\", \"#result\" . Any of the options above can be wrapped into" +
            " parentheses like (#pc). When a cell name is specified, that cell will be printed. The last special values" +
            " have the following meaning:" +
            " #pc - path condition to be printed at each logging step." +
            " #initTerm - full initial term." +
            " #target - full target term." +
            " #result - evaluation result, e.g. full final terms." +
            " The last 3 are printed only at the beginning or end of evaluation respectively." +
            " Options specified without parentheses are printed with toString()." +
            " Options specified in parentheses are pretty-printed. Certain cells have custom formatting." +
            " Pretty-printing options are considerably slower than default toString printing." +
            " Especially when full configuration is printed." +
            " Default value is selected to work with any semantics:" +
            " --log-cells k,#pc,#result" +
            " Recommended alternative:" +
            " --log-cells \"(k),(#pc),#result\"")
    public List<String> logCells = Arrays.asList("k", "#pc", "#result");

    @Parameter(names="--log-rules", description="Log applied rules." +
            "Including \"virtual rewrites\", e.g. rules applied in side conditions of other rules, that in the end " +
            "don't have all their side conditions satisfied and are not applied.")
    public boolean logRules = false;

    @Parameter(names = "--log-func-eval", description = "Log results of function evaluation for every KItem." +
            " Will log initial item and either evaluation result or message \"no rule applicable\"")
    public boolean logFunctionEval = false;

    @Parameter(names="--log-rules-init", description="Log applied rules at initialization phase.")
    public boolean logRulesInit = false;

    @Parameter(names="--debug-z3",
            description="Log formulae fed to z3 together with the rule that triggered them.")
    public boolean debugZ3 = false;

    @Parameter(names="--debug-z3-queries",
            description="Log actual z3 queries. Activates --debug-z3 automatically.")
    public boolean debugZ3Queries = false;

    @Parameter(names = "--debug-formulas", description = "All logging messages of --debug-z3-queries " +
            "+ log all formulas that are attempted to prove. This is the most verbose logging option.")
    public boolean debugFormulas = false;

    public boolean logRulesPublic = false;
    public boolean logFunctionEvalPublic = false;

    @Parameter(names = "--log-success", description = "Log success final states. " +
            "By default only failure final states are logged.")
    public boolean logSuccessFinalStates = false;

    @Parameter(names = "--log-success-pc-diff", description = "Log to stdout the difference between final state path " +
            "condition and initial state path condition, for success paths.")
    public boolean logSuccessPCDiff = false;

    @Parameter(names="--log-progress", description="Print progress bar")
    public boolean logProgress = false;

    @Parameter(names = "--profile-mem-adv",
            description = "Show advanced memory and garbage collector statistics in the " +
                    "summary box. In addition to basic statistics, show statistics after System.gc() invocation " +
                    "and statistics for main runtime caches. " +
                    "WARNING: Execution time with this option is longer because System.gc() is invoked in 3 places.")
    public boolean profileMemAdv = false;

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


package org.kframework.krun;

import java.awt.*;
import java.io.BufferedReader;
import java.io.Console;
import java.io.File;
import java.io.FileInputStream;
import java.io.FilenameFilter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import jline.ArgumentCompletor;
import jline.Completor;
import jline.ConsoleReader;
import jline.FileNameCompletor;
import jline.MultiCompletor;
import jline.SimpleCompletor;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;
import org.fusesource.jansi.AnsiConsole;
import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.backend.java.symbolic.SpecificationCompilerSteps;
import org.kframework.backend.maude.krun.MaudeKRun;
import org.kframework.compile.ConfigurationCleaner;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Configuration;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Definition;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.ListItem;
import org.kframework.kil.Module;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.krun.api.Transition;
import org.kframework.krun.api.UnsupportedBackendOptionException;
import org.kframework.krun.gui.Controller.RunKRunCommand;
import org.kframework.krun.gui.UIDesign.MainWindow;
import org.kframework.parser.DefinitionLoader;
import org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.OptionComparator;

import edu.uci.ics.jung.graph.DirectedGraph;

public class Main {

    private static final String USAGE_KRUN = "krun [options] <file>"
            + K.lineSeparator;
    private static final String USAGE_DEBUG = "Enter one of the following commands without \"--\" in front. "
            + K.lineSeparator
            + "For autocompletion press TAB key and for accessing the command"
            + K.lineSeparator
            + "history use up and down arrows."
            + K.lineSeparator;
    private static final String HEADER_STANDARD = "";
    private static final String FOOTER_STANDARD = "";
    private static final String HEADER_EXPERIMENTAL = "Experimental options:";
    public static final String FOOTER_EXPERIMENTAL
        = K.lineSeparator + "These options are non-standard and subject to change without notice."
        + K.lineSeparator + "In addition you can specify java virtual machine arguments by setting"
        + K.lineSeparator + "the environment variable K_OPTS. Default vm arguments are "
        + K.lineSeparator + "\"-Xss64m -Xmx1024m -Xss8m\", for all K tools on all platforms.";
    public static void printKRunUsageS(CommandlineOptions op) {
        org.kframework.utils.Error.helpMsg(USAGE_KRUN, HEADER_STANDARD, FOOTER_STANDARD, op.getOptionsStandard(), new OptionComparator(op.getOptionList()));
    }
    public static void printKRunUsageE(CommandlineOptions op) {
        org.kframework.utils.Error.helpMsg(USAGE_KRUN, HEADER_EXPERIMENTAL, FOOTER_EXPERIMENTAL, op.getOptionsExperimental(), new OptionComparator(op.getOptionList()));
    }
    public static void printDebugUsage(CommandlineOptions op) {
        org.kframework.utils.Error.helpMsg(USAGE_DEBUG, HEADER_STANDARD, FOOTER_STANDARD, op.getOptionsStandard(), new OptionComparator(op.getOptionList()));
    }
    private static Stopwatch sw = new Stopwatch();

    private static Term parseTerm(String value, Context context) throws Exception {
        org.kframework.parser.concrete.KParser.ImportTblGround(K.compiled_def
                + "/ground/Concrete.tbl");
        ASTNode term = DefinitionLoader.parseCmdString(
                value, "", "Command line argument", context);
        return (Term) term.accept(new FlattenSyntax(context));
    }

    public static Term plug(Map<String, Term> args, Context context) throws TransformerException {
        Configuration cfg = K.kompiled_cfg;
        ASTNode cfgCleanedNode = null;
        try {
            cfgCleanedNode = new ConfigurationCleaner(context).transform(cfg);
        } catch (TransformerException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        Term cfgCleaned;
        if (cfgCleanedNode == null) {
            cfgCleaned = Bag.EMPTY;
        } else {
            if (!(cfgCleanedNode instanceof Configuration)) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.INTERNAL,
                        "Configuration Cleaner failed.", cfg.getFilename(), cfg
                        .getLocation()));
            }
            cfgCleaned = ((Configuration) cfgCleanedNode).getBody();
        }

        if (GlobalSettings.verbose)
            sw.printIntermediate("Plug configuration variables");

        return (Term) cfgCleaned.accept(new SubstitutionFilter(args, context));
    }

    public static Term makeConfiguration(Term kast, String stdin,
                                         RunProcess rp, boolean hasTerm, Context context) throws TransformerException {

        if (hasTerm) {
            if (kast == null) {
                return rp.runParserOrDie(K.parser, K.term, false, null, context);
            } else {
                Error.report("You cannot specify both the term and the configuration\nvariables.");
            }
        }

        HashMap<String, Term> output = new HashMap<String, Term>();
        boolean hasPGM = false;
        Enumeration<Object> en = K.configuration_variables.keys();
        while (en.hasMoreElements()) {
            String name = (String) en.nextElement();
            String value = K.configuration_variables.getProperty(name);
            String parser = K.cfg_parsers.getProperty(name);
            // TODO: get sort from configuration term in definition and pass it
            // here
            Term parsed = null;
            if (parser == null) {
                parser = "kast -groundParser -e";
            }
            parsed = rp.runParserOrDie(parser, value, false, null, context);
            output.put("$" + name, parsed);
            hasPGM = hasPGM || name.equals("$PGM");
        }
        if (!hasPGM && kast != null) {
            output.put("$PGM", kast);
        }
        if (!K.io && stdin == null) {
            stdin = "";
        }
        if (stdin != null) {
            KApp noIO = KApp.of(KLabelConstant.of("'#noIO", context));
            if (K.backend.equals("java")) {
                DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
                if (myList != null) {
                    output.put("$noIO", DataStructureBuiltin.element(myList, noIO));
                }
            } else {
                output.put("$noIO", new ListItem(noIO));
            }
            output.put("$stdin", StringBuiltin.kAppOf(stdin + "\n"));
        } else {
            if (K.backend.equals("java")) {
                DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
                if (myList != null) {
                    output.put("$noIO", DataStructureBuiltin.empty(myList));
                }
            } else {
                output.put("$noIO", org.kframework.kil.List.EMPTY);
            }
            output.put("$stdin", StringBuiltin.EMPTY);
        }

        if (GlobalSettings.verbose)
            sw.printIntermediate("Make configuration");

        return plug(output, context);
    }

    private static KRun obtainKRun(Context context) {
        if (K.backend.equals("maude")) {
            return new MaudeKRun(context);
        } else if (K.backend.equals("java")) {
            try {
                return new JavaSymbolicKRun(context);
            } catch (KRunExecutionException e) {
                Error.report(e.getMessage());
                return null;
            }
        } else {
            Error.report("Currently supported backends are 'maude' and 'java'");
            return null;
        }
    }

    // execute krun in normal mode (i.e. not in debug mode)
    public static void normalExecution(Term KAST, String lang, RunProcess rp,
                                       CommandlineOptions cmd_options, Context context) {
        try {
            CommandLine cmd = cmd_options.getCommandLine();

            KRun krun = obtainKRun(context);
            KRunResult<?> result = null;
            //Set<String> varNames = null;
            Rule patternRule = null;
            RuleCompilerSteps steps;
            steps = new RuleCompilerSteps(K.definition, context);
            try {
                if (cmd.hasOption("pattern") || "search".equals(K.maude_cmd)) {
                    org.kframework.parser.concrete.KParser
                            .ImportTbl(K.compiled_def + "/def/Concrete.tbl");
                    ASTNode pattern = DefinitionLoader.parsePattern(K.pattern,
                            "Command line pattern", context);
                    CollectVariablesVisitor vars = new CollectVariablesVisitor(context);
                    pattern.accept(vars);
                    //varNames = vars.getVars().keySet();

                    try {
                        pattern = steps.compile(new Rule((Sentence) pattern), null);
                    } catch (CompilerStepDone e) {
                        pattern = (ASTNode) e.getResult();
                    }
                    patternRule = new Rule((Sentence) pattern);
                    if (GlobalSettings.verbose)
                        sw.printIntermediate("Parsing search pattern");
                }

                if (K.do_search) {
                    if ("search".equals(K.maude_cmd)) {
                        BufferedReader br = new BufferedReader(
                                new InputStreamReader(System.in));
                        String buffer = "";
                        // detect if the input comes from console or redirected
                        // from a pipeline
                        Console c = System.console();
                        if (c == null && br.ready()) {
                            try {
                                buffer = br.readLine();
                            } catch (IOException ioe) {
                                ioe.printStackTrace();
                            } finally {
                                if (br != null) {
                                    try {
                                        br.close();
                                    } catch (IOException e) {
                                        e.printStackTrace();
                                    }
                                }
                            }
                        }
                        Integer depth = null;
                        Integer bound = null;
                        if (cmd.hasOption("bound") && cmd.hasOption("depth")) {
                            bound = Integer.parseInt(K.bound);
                            depth = Integer.parseInt(K.depth);
                        } else if (cmd.hasOption("bound")) {
                            bound = Integer.parseInt(K.bound);
                        } else if (cmd.hasOption("depth")) {
                            depth = Integer.parseInt(K.depth);
                        }
                        if(K.do_testgen){
                            result = krun.generate(bound,
                                    depth,
                                    K.searchType,
                                    patternRule,
                                    makeConfiguration(KAST, buffer, rp,
                                            (K.term != null), context), steps);
                        } else{
                            result = krun.search(
                                    bound,
                                    depth,
                                    K.searchType,
                                    patternRule,
                                    makeConfiguration(KAST, buffer, rp,
                                            (K.term != null), context), steps);
                        }

                        if (GlobalSettings.verbose)
                            sw.printTotal("Search total");
                    } else {
                        Error.report("For the search option you must specify that --maude-cmd=search");
                    }
                } else if (K.model_checking.length() > 0) {
                    // run kast for the formula to be verified
                    File formulaFile = new File(K.model_checking);
                    Term KAST1 = null;
                    if (!formulaFile.exists()) {
                        // Error.silentReport("\nThe specified argument does not exist as a file on the disc; it may represent a direct formula: "
                        // + K.model_checking);
                        // assume that the specified argument is not a file and
                        // maybe represents a formula
                        KAST1 = rp.runParserOrDie("kast -e", K.model_checking, false,
                                "LtlFormula", context);
                    } else {
                        // the specified argument represents a file
                        KAST1 = rp.runParserOrDie("kast", K.model_checking, false,
                                "LtlFormula", context);
                    }

                    result = krun
                            .modelCheck(
                                    KAST1,
                                    makeConfiguration(KAST, null, rp,
                                            (K.term != null), context));

                    if (GlobalSettings.verbose)
                        sw.printTotal("Model checking total");
                } else if (K.prove.length() > 0) {
                    File proofFile = new File(K.prove);
                    if (!proofFile.exists()) {
                        Error.report("Cannot find the file containing rules to prove");
                    }
                    String content = FileUtil.getFileContent(proofFile.getAbsolutePath());
                    Definition parsed = DefinitionLoader.parseString(content,
                            proofFile.getAbsolutePath(), context);
                    Module mod = parsed.getSingletonModule();
                    try {
                        mod = new SpecificationCompilerSteps(context).compile(mod, null);
                    } catch (CompilerStepDone e) {
                        assert false: "dead code";
                    }
                    result = krun.prove(mod);
                } else if (cmd.hasOption("depth")) {
                    int depth = Integer.parseInt(K.depth);
                    result = krun.step(makeConfiguration(KAST, null, rp,
                            (K.term != null), context), depth);

                    if (GlobalSettings.verbose)
                        sw.printTotal("Bounded execution total");
                } else {
                    result = krun.run(makeConfiguration(KAST, null, rp,
                            (K.term != null), context));

                    if (GlobalSettings.verbose)
                        sw.printTotal("Normal execution total");
                }

                if (cmd.hasOption("pattern") && !K.do_search) {
                    Object krs = result.getResult();
                    if (krs instanceof KRunState) {
                        Term res = ((KRunState) krs).getRawResult();
                        krun.setBackendOption("io", false);
                        result = krun.search(null, null, K.searchType, patternRule, res, steps);
                    }else {
                        Error.report("Pattern matching after execution is not supported by search\nand model checking");
                    }
                }

            } catch (KRunExecutionException e) {
                rp.printError(e.getMessage(), lang, context);
                System.exit(1);
            } catch (TransformerException e) {
                e.report();
            } catch (UnsupportedBackendOptionException e) {
                Error.report("Backend \"" + K.backend + "\" does not support option " + e.getMessage());
            }

            if ("pretty".equals(K.output_mode)) {
                String output = result.toString();
                if (!cmd.hasOption("output")) {
                    AnsiConsole.out.println(output);
                } else {
                    FileUtil.createFile(K.output, output);
                }
                // print search graph
                if ("search".equals(K.maude_cmd) && K.do_search
                        && K.showSearchGraph) {
                    System.out.println(K.lineSeparator + "The search graph is:"
                            + K.lineSeparator);
                    @SuppressWarnings("unchecked")
                    KRunResult<SearchResults> searchResult = (KRunResult<SearchResults>) result;
                    AnsiConsole.out
                            .println(searchResult.getResult().getGraph());
                    // offer the user the possibility to turn execution into
                    // debug mode
                    while (true) {
                        System.out.print(K.lineSeparator
                                + "Do you want to enter in debug mode? (y/n):");
                        BufferedReader stdin = new BufferedReader(
                                new InputStreamReader(System.in));
                        String input = stdin.readLine();
                        if (input == null) {
                            K.debug = false;
                            K.guidebug = false;
                            System.out.println();
                            break;
                        }
                        if (input.equals("y")) {
                            K.debug = true;
                            debugExecution(KAST, lang, searchResult, context);
                        } else if (input.equals("n")) {
                            K.debug = false;
                            K.guidebug = false;
                            break;
                        } else {
                            System.out
                                    .println("You should specify one of the possible answers:y or n");
                        }
                    }
                }
            } else if ("raw".equals(K.output_mode)) {
                String output = result.getRawOutput();
                ;
                if (!cmd.hasOption("output")) {
                    System.out.println(output);
                } else {
                    FileUtil.createFile(K.output, output);
                }
            } else if ("none".equals(K.output_mode)) {
                System.out.print("");
            } else if ("binary".equals(K.output_mode)) {
                Object krs = result.getResult();
                if (krs instanceof KRunState) {
                    Term res = ((KRunState) krs).getRawResult();

                    if (!cmd.hasOption("output")) {
                        Error.silentReport("Did not specify an output file. Cannot print output-mode binary to\nstandard out. Saving to .k/krun/krun_output");
                        BinaryLoader.toBinary(res, new FileOutputStream(
                                K.krun_output));
                    } else {
                        BinaryLoader.toBinary(res, new FileOutputStream(
                                K.output));
                    }
                } else {
                    Error.report("binary output mode is not supported by search and model\nchecking");
                }

            } else {
                Error.report(K.output_mode
                        + " is not a valid value for output-mode option");
            }

            System.exit(0);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    // execute krun in debug mode (i.e. step by step execution)
    // isSwitch variable is true if we enter in debug execution from normal
    // execution (we use the search command with --graph option)
    @SuppressWarnings("unchecked")
    public static void debugExecution(Term kast, String lang,
                                      KRunResult<SearchResults> state, org.kframework.kil.loader.Context context) {
        try {
            // adding autocompletion and history feature to the stepper internal
            // commandline by using the JLine library
            ConsoleReader reader = new ConsoleReader();
            reader.setBellEnabled(false);

            List<Completor> argCompletor = new LinkedList<Completor>();
            argCompletor.add(new SimpleCompletor(new String[] { "help",
                    "abort", "resume", "step", "step-all", "select",
                    "show-search-graph", "show-node", "show-edge", "save", "load", "read" }));
            argCompletor.add(new FileNameCompletor());
            List<Completor> completors = new LinkedList<Completor>();
            completors.add(new ArgumentCompletor(argCompletor));
            reader.addCompletor(new MultiCompletor(completors));

            new File(K.compiled_def + K.fileSeparator + "main.maude")
                    .getCanonicalPath();
            RunProcess rp = new RunProcess();
            KRun krun = obtainKRun(context);
            krun.setBackendOption("io", false);
            KRunDebugger debugger;
            try {
                if (state == null) {
                    Term t = makeConfiguration(kast, "", rp, (K.term != null), context);
                    debugger = krun.debug(t);
                    System.out
                            .println("After running one step of execution the result is:");
                    AnsiConsole.out.println(debugger.printState(debugger
                            .getCurrentState()));
                } else {
                    debugger = krun.debug(state.getResult().getGraph());
                }
            } catch (UnsupportedBackendOptionException e) {
                Error.report("Backend \"" + K.backend + "\" does not support option " + e.getMessage());
                throw e; //unreachable
            }
            while (true) {
                System.out.println();
                String input = reader.readLine("Command > ");
                if (input == null) {
                    // probably pressed ^D
                    System.out.println();
                    System.exit(0);
                }

                // construct the right command line input when we specify the
                // "step" option with an argument (i.e. step=3)
                input = input.trim();
                String[] tokens = input.split(" ");
                // store the tokens that are not a blank space
                List<String> items = new ArrayList<String>();
                for (int i = 0; i < tokens.length; i++) {
                    if ((!(tokens[i].equals(" ")) && (!tokens[i].equals("")))) {
                        items.add(tokens[i]);
                    }
                }
                StringBuilder aux = new StringBuilder();
                // excepting the case of a command like: help
                if (items.size() > 1) {
                    for (int i = 0; i < items.size(); i++) {
                        if (i > 0) {
                            aux.append("=");
                            aux.append(items.get(i));
                        } else if (i == 0) {
                            aux.append(items.get(i));
                        }
                    }
                    input = aux.toString();
                }
                // apply trim to remove possible blank spaces from the inserted
                // command
                String[] cmds = new String[] { "--" + input };
                CommandlineOptions cmd_options = new CommandlineOptions();
                CommandLine cmd = cmd_options.parse(cmds);
                // when an error occurred during parsing the commandline
                // continue the execution of the stepper
                if (cmd == null) {
                    continue;
                } else {
                    if (cmd.hasOption("help")) {
                        printDebugUsage(cmd_options);
                    }
                    if (cmd.hasOption("abort")) {
                        System.exit(0);
                    }
                    if (cmd.hasOption("resume")) {
                        try {
                            debugger.resume();
                            AnsiConsole.out.println(debugger
                                    .printState(debugger.getCurrentState()));
                        } catch (IllegalStateException e) {
                            Error.silentReport("Wrong command: If you previously used the step-all command you must"
                                    + K.lineSeparator
                                    + "seletc first a solution with step command before executing steps of rewrites!");
                        }
                    }
                    // one step execution (by default) or more if you specify an
                    // argument
                    if (cmd.hasOption("step")) {
                        // by default execute only one step at a time
                        String arg = new String("1");
                        String[] remainingArguments = null;
                        remainingArguments = cmd.getArgs();
                        if (remainingArguments.length > 0) {
                            arg = remainingArguments[0];
                        }
                        try {
                            int steps = Integer.parseInt(arg);
                            debugger.step(steps);
                            AnsiConsole.out.println(debugger
                                    .printState(debugger.getCurrentState()));
                        } catch (NumberFormatException e) {
                            Error.silentReport("Argument to step must be an integer.");
                        } catch (IllegalStateException e) {
                            Error.silentReport("Wrong command: If you previously used the step-all command you must"
                                    + K.lineSeparator
                                    + "select first a solution with step command before executing steps of rewrites!");
                        }
                    }
                    if (cmd.hasOption("step-all")) {
                        // by default compute all successors in one transition
                        String arg = new String("1");
                        String[] remainingArguments = null;
                        remainingArguments = cmd.getArgs();
                        if (remainingArguments.length > 0) {
                            arg = remainingArguments[0];
                        }
                        try {
                            int steps = Integer.parseInt(arg);
                            SearchResults states = debugger.stepAll(steps);
                            AnsiConsole.out.println(states);

                        } catch (NumberFormatException e) {
                            Error.silentReport("Argument to step-all must be an integer.");
                        } catch (IllegalStateException e) {
                            Error.silentReport("Wrong command: If you previously used the step-all command you must"
                                    + K.lineSeparator
                                    + "select first a solution with step command before executing steps of rewrites!");
                        }
                    }
                    // "select n7" or "select 3" are both valid commands
                    if (cmd.hasOption("select")) {
                        String arg = new String();
                        arg = cmd.getOptionValue("select").trim();
                        try {
                            int stateNum = Integer.parseInt(arg);
                            debugger.setCurrentState(stateNum);
                            AnsiConsole.out.println(debugger
                                    .printState(debugger.getCurrentState()));
                        } catch (NumberFormatException e) {
                            Error.silentReport("Argument to select must bean integer.");
                        } catch (IllegalArgumentException e) {
                            System.out
                                    .println("A node with the specified state number could not be found in the"
                                            + K.lineSeparator + "search graph");
                        }
                    }
                    if (cmd.hasOption("show-search-graph")) {
                        System.out.println(K.lineSeparator
                                + "The search graph is:" + K.lineSeparator);
                        System.out.println(debugger.getGraph());
                    }
                    if (cmd.hasOption("show-node")) {
                        String nodeId = cmd.getOptionValue("show-node").trim();
                        try {
                            int stateNum = Integer.parseInt(nodeId);
                            AnsiConsole.out.println(debugger
                                    .printState(stateNum));
                        } catch (NumberFormatException e) {
                            Error.silentReport("Argument to select node to show must be an integer.");
                        } catch (IllegalArgumentException e) {
                            System.out
                                    .println("A node with the specified state number could not be found in the"
                                            + K.lineSeparator + "search graph");
                        }
                    }
                    if (cmd.hasOption("show-edge")) {
                        String[] vals = cmd.getOptionValues("show-edge");
                        vals = vals[0].split("=", 2);
                        try {
                            int state1 = Integer.parseInt(vals[0].trim());
                            int state2 = Integer.parseInt(vals[1].trim());
                            AnsiConsole.out.println(debugger.printEdge(state1,
                                    state2));
                        } catch (ArrayIndexOutOfBoundsException e) {
                            Error.silentReport("Must specify two nodes with an edge between them.");
                        } catch (NumberFormatException e) {
                            Error.silentReport("Arguments to select edge to show must be integers.");
                        } catch (IllegalArgumentException e) {
                            System.out
                                    .println("An edge with the specified endpoints could not be found in the"
                                            + K.lineSeparator + "search graph");
                        }
                    }

                    DirectedGraph<KRunState, Transition> savedGraph = null;
                    if(cmd.hasOption("save")) {
                        BinaryLoader.toBinary(debugger.getGraph(), new FileOutputStream(new File(cmd.getOptionValue("save")).getCanonicalPath()));
                        System.out.println("File successfully saved.");
                    }
                    if (cmd.hasOption("load")) {
                        try {
                            savedGraph = (DirectedGraph<KRunState, Transition>) BinaryLoader.fromBinary(new FileInputStream(cmd.getOptionValue("load")));
                            krun = new MaudeKRun(context);
                            debugger = krun.debug(savedGraph);
                            debugger.setCurrentState(1);
                            System.out.println("File successfully loaded.");
                        } catch (FileNotFoundException e) {
                            System.out.println("There is no such file, please try again.");
                        }
                    }
                    if (cmd.hasOption("read")) {
                        try {
                            debugger.readFromStdin(StringBuiltin.valueOf("\"" +
                                    cmd.getOptionValue("read") + "\"").stringValue());
                            AnsiConsole.out.println(
                                    debugger.printState(debugger.getCurrentState()));
                        } catch (IllegalStateException e) {
                            Error.silentReport(e.getMessage());
                        }
                    }
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    public static void guiDebugExecution(Term kast, String lang,
                                         KRunResult<SearchResults> state, Context context) {
		
        try {
			KRun krun = obtainKRun(context);
			krun.setBackendOption("io",false);
            new MainWindow(new RunKRunCommand(kast, lang, false,krun), context);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /**
     * @param cmds
     *            represents the arguments/options given to krun command..
     */
    public static void execute_Krun(String cmds[]) {
        Context context = new Context();
        K.init(context);
        // delete temporary krun directory
        try {
            FileUtil.deleteDirectory(new File(K.krunDir));
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
        Runtime.getRuntime().addShutdownHook(new Thread() {
            public void run() {
                try {
                    FileUtil.renameFolder(K.krunTempDir, K.krunDir);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        });

        CommandlineOptions cmd_options = new CommandlineOptions();
        CommandLine cmd = cmd_options.parse(cmds);
        if (cmd == null) {
            printKRunUsageS(cmd_options);
         /* printKRunUsageE(cmd_options); */ /* TODO: Switch to this when the user has tried to use an experimental option. */
            System.exit(1);
        }

        // set verbose
        if (cmd.hasOption("verbose")) {
            GlobalSettings.verbose = true;
        }

        // set fast-kast
        if (cmd.hasOption("fast-kast")) {
            GlobalSettings.fastKast = !GlobalSettings.fastKast;
        }

        if (GlobalSettings.verbose)
            sw.printIntermediate("Deleting temporary krun directory");

        try {

            // Parse the program arguments

            if (cmd.hasOption("search")
                    || cmd.hasOption("search-final")
                    || cmd.hasOption("search-all")
                    || cmd.hasOption("search-one-step")
                    || cmd.hasOption("search-one-or-more-steps")) {
                K.maude_cmd = "search";
                K.io = false;
                K.do_search = true;
                if (cmd.hasOption("search") && cmd.hasOption("depth")) {
                    K.searchType = SearchType.STAR;
                }
            }
            if (cmd.hasOption("search-final")) {
                K.searchType = SearchType.FINAL;
            }
            if (cmd.hasOption("search-all")) {
                K.searchType = SearchType.STAR;
            }
            if (cmd.hasOption("search-one-step")) {
                K.searchType = SearchType.ONE;
            }
            if (cmd.hasOption("search-one-or-more-steps")) {
                K.searchType = SearchType.PLUS;
            }
            if (cmd.hasOption("help")) {
                K.help = true;
            }
            if (cmd.hasOption("help-experimental")) {
                K.helpExperimental = true;
            }
            if (cmd.hasOption("version")) {
                K.version = true;
            }
            // CLEANUP_OPTIONS: The option --directory was added, replacing --k-definition and --compiled-def.
            if (cmd.hasOption("directory")) {
                K.directory = new File(cmd.getOptionValue("directory")).getCanonicalPath();
                org.kframework.utils.Error.checkIfInputDirectory(K.directory);
            }
            if (cmd.hasOption("main-module")) {
                K.main_module = cmd.getOptionValue("main-module");
            }
            if (cmd.hasOption("syntax-module")) {
                K.syntax_module = cmd.getOptionValue("syntax-module");
            }
            if (cmd.hasOption("parser")) {
                K.parser = cmd.getOptionValue("parser");
            }
            if (cmd.hasOption("term")) {
                K.term = cmd.getOptionValue("term");
            }
            if (cmd.hasOption("io")) {
                String v = cmd.getOptionValue("io");
                if (v.equals("on"))
                    K.io = true;
                else if (v.equals("off"))
                    K.io = false;
                else
                    Error.report("Unrecognized option: --io " + v + "\nUsage: krun --io [on|off]");
            }
            if (cmd.hasOption("statistics")) {
                String v = cmd.getOptionValue("statistics");
                if (v.equals("on"))
                    K.statistics = true;
                else if (v.equals("off"))
                    K.statistics = false;
                else
                    Error.report("Unrecognized option: --statistics " + v + "\nUsage: krun --statistics [on|off]");
            }
            if (cmd.hasOption("color")) {
                String v = cmd.getOptionValue("color");
                if (v.equals("on"))
                    K.color = ColorSetting.ON;
                else if (v.equals("off"))
                    K.color = ColorSetting.OFF;
                else if (v.equals("extended"))
                    K.color = ColorSetting.EXTENDED;
                else
                    Error.report("Unrecognized option: --color " + v + "\nUsage: krun --color [on|off|extended]");
            }
            if (cmd.hasOption("terminal-color")) {
                String v = cmd.getOptionValue("terminal-color");
                Color terminalColor = ColorUtil.getColorByName(v);
                if (terminalColor != null) {
                    K.terminalColor = terminalColor;
                } else {
                    Error.report("Invalid terminal color: " + v);
                }
            }

            if (cmd.hasOption("parens")) {
                String v = cmd.getOptionValue("parens");
                if (v.equals("greedy")) {
                    K.parens = true;
                } else if (v.equals("smart")) {
                    K.parens = false;
                } else {
                    Error.report("Unrecognized option: --parens " + v + "\nUsage: krun --parens [greedy|smart]");
                }
            }

            //testcase generation
            if (cmd.hasOption("generate-tests")) {
                K.do_testgen = true;
                K.io = false;
                K.do_search = true;
            }
            if (cmd.hasOption("maude-cmd")) {
                K.maude_cmd = cmd.getOptionValue("maude-cmd");
            }
			/*
			 * if (cmd.hasOption("xsearch-pattern")) { K.maude_cmd = "search";
			 * K.do_search = true; K.xsearch_pattern =
			 * cmd.getOptionValue("xsearch-pattern"); //
			 * System.out.println("xsearch-pattern:" + K.xsearch_pattern); }
			 */
            if (cmd.hasOption("pattern")) {
                K.pattern = cmd.getOptionValue("pattern");
            }
            if (cmd.hasOption("bound")) {
                K.bound = cmd.getOptionValue("bound");
            }
            if (cmd.hasOption("depth")) {
                K.depth = cmd.getOptionValue("depth");
            }
            if (cmd.hasOption("graph")) {
                K.showSearchGraph = true;
            }
            if (cmd.hasOption("output-mode")) {
                K.output_mode = cmd.getOptionValue("output-mode");
            }
            if (cmd.hasOption("log-io")) {
                String v = cmd.getOptionValue("log-io");
                if (v.equals("on"))
                    K.log_io = true;
                else if (v.equals("off"))
                    K.log_io = false;
                else
                    Error.report("Unrecognized option: --log-io " + v + "\nUsage: krun --log-io [on|off]");
            }
            if (cmd.hasOption("debug")) {
                K.debug = true;
            }
            if (cmd.hasOption("debug-gui")) {
                K.guidebug = true;
            }
            if (cmd.hasOption("trace")) {
                K.trace = true;
            }
            if (cmd.hasOption("profile")) {
                K.profile = true;
            }
            if (cmd.hasOption("ltlmc")) {
                K.model_checking = cmd.getOptionValue("ltlmc");
            }
            if (cmd.hasOption("prove")) {
                K.prove = cmd.getOptionValue("prove");
            }
            if (cmd.hasOption("smt")) {
                K.smt = cmd.getOptionValue("smt");
            }
            if (cmd.hasOption("output")) {
                if (!cmd.hasOption("color")) {
                    K.color = ColorSetting.OFF;
                }
                K.output = new File(cmd.getOptionValue("output"))
                        .getCanonicalPath();
            }
            if (cmd.hasOption("c")) {

                if (K.term != null) {
                    Error.report("You cannot specify both the term and the configuration\nvariables.");
                }

                K.configuration_variables = cmd.getOptionProperties("c");
                String parser = null;
                for (Option opt : cmd.getOptions()) {
                    if (opt.equals(cmd_options.getOptions().getOption("c"))
                            && parser != null) {
                        K.cfg_parsers.setProperty(opt.getValue(0), parser);
                    }
                    if (opt.equals(cmd_options.getOptions().getOption(
                            "cfg-parser"))) {
                        parser = opt.getValue();
                    }
                }
            }
            if (cmd.hasOption("backend")) {
                K.backend = cmd.getOptionValue("backend");
            }
            // printing the output according to the given options
            if (K.help) {
                printKRunUsageS(cmd_options);
                System.exit(0);
            }
            if (K.helpExperimental) {
                printKRunUsageE(cmd_options);
                System.exit(0);
            }
            if (K.version) {
                String msg = org.kframework.utils.file.FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
                System.out.println(msg);
                System.exit(0);
            }

            String[] remainingArguments = null;
            if (cmd_options.getCommandLine().getOptions().length > 0) {
                remainingArguments = cmd.getArgs();
            } else {
                remainingArguments = cmds;
            }
            String programArg = new String();
            if (remainingArguments.length > 0) {
                programArg = remainingArguments[0];
                K.pgm = programArg;
            }
            String lang = null;
            if (K.pgm != null) {
                File pgmFile = new File(K.pgm);
                if (pgmFile.exists()) {
                    lang = FileUtil.getExtension(K.pgm, ".", K.fileSeparator);
                }
            }

            if (GlobalSettings.verbose)
                sw.printIntermediate("Parsing command line options");

            /* CLEANUP_OPTIONS */
            if (!cmd.hasOption("directory")) {
                K.directory = new File(K.userdir).getCanonicalPath();
            }
            {
                // search for the definition
                File[] dirs = new File(K.directory).listFiles(new FilenameFilter() {
                    @Override
                    public boolean accept(File current, String name) {
                        return new File(current, name).isDirectory();
                    }
                });

                K.compiled_def = null;
                for (int i = 0; i < dirs.length; i++) {
                    if (dirs[i].getAbsolutePath().endsWith("-kompiled")) {
                        if (K.compiled_def != null) {
                            String msg = "Multiple compiled definitions found.";
                            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
                        } else {
                            K.compiled_def = dirs[i].getAbsolutePath();
                        }
                    }
                }

                if (K.compiled_def == null) {
                    String msg = "Could not find a compiled definition.";
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
                }
            }

            if (K.compiled_def == null) {
                Error.report("Could not find a compiled K definition. Please ensure that\neither a compiled K definition exists in the current directory with its default\nname, or that --directory has been specified.");
            }
            File compiledFile = new File(K.compiled_def);
            if (!compiledFile.exists()) {
                Error.report("\nCould not find compiled definition: "
                        + K.compiled_def
                        + "\nPlease compile the definition by using `kompile'.");
            }

            context.dotk = new File(
                    new File(K.compiled_def).getParent() + File.separator
                            + ".k");
            if (!context.dotk.exists()) {
                context.dotk.mkdirs();
            }
            context.kompiled = new File(K.compiled_def);
            K.kdir = context.dotk.getCanonicalPath();
            K.setKDir();
			/*
			 * System.out.println("K.k_definition=" + K.k_definition);
			 * System.out.println("K.syntax_module=" + K.syntax_module);
			 * System.out.println("K.main_module=" + K.main_module);
			 * System.out.println("K.compiled_def=" + K.compiled_def);
			 */

            if (GlobalSettings.verbose)
                sw.printIntermediate("Checking compiled definition");

            // in KAST variable we obtain the output from running kast process
            // on a program defined in K
            Term KAST = null;
            RunProcess rp = new RunProcess();

            if (!context.initialized) {
                String path = K.compiled_def + "/defx-" + K.backend + ".bin";
                Definition javaDef;
                if (new File(path).exists()) {
                    javaDef = (Definition) BinaryLoader
                            .fromBinary(new FileInputStream(K.compiled_def
                                    + "/defx-" + K.backend + ".bin"));
                } else {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                            KExceptionGroup.CRITICAL,
                            "Could not find compiled definition for backend '" + K.backend + "'.  " +
                                    "Please ensure this backend has been kompiled."));
                    throw new AssertionError("unreachable");
                }

                if (GlobalSettings.verbose)
                    sw.printIntermediate("Reading definition from binary");

                // This is essential for generating maude
                javaDef = new FlattenModules(context).compile(javaDef, null);

                if (GlobalSettings.verbose)
                    sw.printIntermediate("Flattening modules");

                try {
                    javaDef = (Definition) javaDef
                            .accept(new AddTopCellConfig(context));
                } catch (TransformerException e) {
                    e.report();
                }

                if (GlobalSettings.verbose)
                    sw.printIntermediate("Adding top cell to configuration");

                javaDef.preprocess(context);

                if (GlobalSettings.verbose)
                    sw.printIntermediate("Preprocessing definition");

                K.definition = javaDef;

                if (GlobalSettings.verbose)
                    sw.printIntermediate("Importing tables");

                org.kframework.kil.Configuration configKompiled = (org.kframework.kil.Configuration) BinaryLoader
                        .fromBinary(new FileInputStream(K.compiled_def
                                + "/configuration.bin"));

                CommandLine compileOptions = (CommandLine) BinaryLoader
                        .fromBinary(new FileInputStream(K.compiled_def +
                                "/compile-options.bin"));
                if (compileOptions.hasOption("sortCells"))
                    GlobalSettings.sortedCells = true;

                K.kompiled_cfg = configKompiled;

                if (GlobalSettings.verbose)
                    sw.printIntermediate("Reading configuration from binary");
            }

            if (!cmd.hasOption("main-module")) {
                K.main_module = K.definition.getMainModule();
            }
            if (!cmd.hasOption("syntax-module")) {
                K.syntax_module = K.definition.getMainSyntaxModule();
            }

            if (GlobalSettings.verbose)
                sw.printIntermediate("Resolving main and syntax modules");

            if (K.pgm != null) {
                KAST = rp.runParserOrDie(K.parser, K.pgm, false, null, context);
            } else {
                KAST = null;
            }

            if (GlobalSettings.verbose)
                sw.printIntermediate("Kast process");

            if (K.term != null) {
                if (K.parser.equals("kast") && !cmd.hasOption("parser")) {
                    if (K.backend.equals("java")) {
                        K.parser = "kast -ruleParser";
                    } else {
                        K.parser = "kast -groundParser";
                    }
                }
            }

            GlobalSettings.kem.print();

            if (!K.debug && !K.guidebug) {
                normalExecution(KAST, lang, rp, cmd_options, context);
            } else {
                if (K.do_search) {
                    Error.report("Cannot specify --search with --debug. In order to search\nnside the debugger, use the step-all command.");
                }
                if (K.guidebug)
                    guiDebugExecution(KAST, lang, null, context);
                else
                    debugExecution(KAST, lang, null, context);
            }
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    public static void main(String[] args) {
        execute_Krun(args);
    }
}

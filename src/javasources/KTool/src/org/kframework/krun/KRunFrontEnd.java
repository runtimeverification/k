// Copyright (c) 2010-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import static org.apache.commons.io.FileUtils.writeStringToFile;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.LinkedList;
import java.util.List;

import jline.ArgumentCompletor;
import jline.Completor;
import jline.ConsoleReader;
import jline.FileNameCompletor;
import jline.MultiCompletor;
import jline.SimpleCompletor;

import org.fusesource.jansi.AnsiString;
import org.kframework.backend.java.ksimulation.Waitor;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.backend.maude.krun.MaudeKRun;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.kompile.KompileOptions.Backend;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.KRunOptions.OutputMode;
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
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.SortedParameterDescriptions;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;

import edu.uci.ics.jung.graph.DirectedGraph;

public class KRunFrontEnd {

    private static Stopwatch sw = Stopwatch.instance();

    private static KRun obtainKRun(Context context) {
        if (context.kompileOptions.backend == Backend.MAUDE
                || context.kompileOptions.backend == Backend.SYMBOLIC) {
            return new MaudeKRun(context, sw);
        } else if (context.kompileOptions.backend == Backend.JAVA) {
            return new JavaSymbolicKRun(context);
        } else {
            throw new AssertionError("currently only three execution backends are supported: "
                    + "MAUDE, SYMBOLIC, and JAVA");
        }
    }

    /**
     * Execute krun in normal mode (i.e. not in debug mode).
     * @param executionContext the object containing the initial configuration
     * and definition context to use to execute.
     * @return true if the application completed normally; false otherwise
     */
    public static boolean normalExecution(ExecutionContext executionContext) {
        Term initialConfiguration = executionContext.getInitialConfiguration();
        Context context = executionContext.getContext();

        try {
            KRunOptions options = context.krunOptions;
            KRun krun = obtainKRun(context);
            KRunResult<?> result = null;
            //Set<String> varNames = null;
            try {
                Rule patternRule = null;
                RuleCompilerSteps steps = null;
                if (options.pattern(context) != null) {
                    steps = new RuleCompilerSteps(context);
                    ASTNode pattern = options.pattern(context);
                    CollectVariablesVisitor vars = new CollectVariablesVisitor(context);
                    vars.visitNode(pattern);
                    //varNames = vars.getVars().keySet();

                    try {
                        pattern = steps.compile(new Rule((Sentence) pattern), null);
                    } catch (CompilerStepDone e) {
                        pattern = (ASTNode) e.getResult();
                    }
                    patternRule = new Rule((Sentence) pattern);
                    sw.printIntermediate("Parsing search pattern");
                }
                if (options.search()) {

                    if(options.experimental.javaExecution.generateTests){
                        result = krun.generate(
                                options.bound,
                                options.depth,
                                options.searchType(),
                                patternRule,
                                initialConfiguration, steps);
                    } else{
                        result = krun.search(
                                options.bound,
                                options.depth,
                                options.searchType(),
                                patternRule,
                                initialConfiguration, steps);
                    }

                    sw.printTotal("Search total");
                } else if (options.experimental.ltlmc() != null) {
                    Term formula = new RunProcess().runParserOrDie("kast -e",
                            options.experimental.ltlmc(), false, "LtlFormula", context);

                    result = krun.modelCheck(
                                    formula,
                                    initialConfiguration);

                    sw.printTotal("Model checking total");
                } else if (options.experimental.prove() != null) {
                    File proofFile = options.experimental.prove();
                    String content = FileUtil.getFileContent(
                            proofFile.getAbsoluteFile().toString());
                    Definition parsed = DefinitionLoader.parseString(content,
                            proofFile.getAbsolutePath(), context);
                    Module mod = parsed.getSingletonModule();
                    result = krun.prove(mod, initialConfiguration);
                    sw.printTotal("Proof total");
                } else if (options.depth != null) {
                    result = krun.step(initialConfiguration, options.depth);
                    sw.printTotal("Bounded execution total");
                } else {
                    result = krun.run(initialConfiguration);
                    sw.printTotal("Normal execution total");
                }
                if (patternRule != null && !options.search()) {
                    Object krs = result.getResult();
                    assert krs instanceof KRunState;
                    Term res = ((KRunState) krs).getRawResult();
                    krun.setBackendOption("io", false);
                    result = krun.search(1, 1, SearchType.FINAL, patternRule, res, steps);
                }

            } catch (KRunExecutionException e) {
                if (context.globalOptions.debug) {
                    e.printStackTrace();
                }
                new RunProcess().printError(e.getMessage());
                return false;
            } catch (ParseFailedException e) {
                e.report();
            } catch (UnsupportedBackendOptionException e) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL, "Backend \""
                                + context.kompileOptions.backend.name().toLowerCase()
                                + "\" does not support option " + e.getMessage()));
            }

            if (options.output.isPrettyPrinting()) {

                String output = result.toString();

                writeOutput(options, output);
                // print search graph
                if (options.search() && options.graph) {
                    System.out.println(K.lineSeparator + "The search graph is:"
                            + K.lineSeparator);
                    @SuppressWarnings("unchecked")
                    KRunResult<SearchResults> searchResult = (KRunResult<SearchResults>) result;
                    System.out.println(searchResult.getResult().getGraph());
                    // offer the user the possibility to turn execution into
                    // debug mode
                    while (true) {
                        System.out.print(K.lineSeparator
                                + "Do you want to enter in debug mode? (y/n):");
                        BufferedReader stdin = new BufferedReader(
                                new InputStreamReader(System.in));
                        System.out.flush();
                        String input = stdin.readLine();
                        if (input == null || input.equals("n")) {
                            System.out.println();
                            break;
                        } else if (input.equals("y")) {
                            debugExecution(executionContext, searchResult);
                            break;
                        } else {
                            System.out
                                    .println("You should specify one of the possible answers:y or n");
                        }
                    }
                }
            } else if (options.output == OutputMode.RAW) {
                String output = result.getRawOutput();
                writeOutput(options, output);
            } else if (options.output == OutputMode.NONE) {
            } else if (options.output == OutputMode.BINARY) {
                Object krs = result.getResult();
                if (krs instanceof KRunState) {
                    Term res = ((KRunState) krs).getRawResult();

                    if (options.experimental.outputFile == null) {
                        BinaryLoader.saveOrDie(System.out, res);

                    } else {
                        BinaryLoader.saveOrDie(options.experimental.outputFile.getAbsolutePath(), res);
                    }
                } else {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                            "Binary output mode is not supported by search and model checking"));
                }

            }
        } catch (IOException e) {
            e.printStackTrace();
            return false;
        }
        return true;
    }
    private static void writeOutput(KRunOptions options, String output)
            throws IOException {
        if (options.experimental.outputFile == null) {
            System.out.println(output);
        } else {
            output = new AnsiString(output).getPlain().toString();
            writeStringToFile(options.experimental.outputFile, output);
        }
    }

    private static Object command(JCommander jc) {
        return jc.getCommands().get(jc.getParsedCommand()).getObjects().get(0);
    }

    /**
     *  execute krun in debug mode (i.e. step by step execution)
     * state is not null if we enter in debug execution from normal
     * execution (we use the search command with --graph option)
     * @param initialConfiguration The initial configuration to execute with in the debugger
     * @param state An optional set of search results to initialize with the initial state of the debugger.
     * @param context The definition context loaded from the compiled definition.
     * @return true if the application completed normally; false otherwise
     */
    @SuppressWarnings("unchecked")
    public static boolean debugExecution(ExecutionContext executionContext,
                                      KRunResult<SearchResults> state) {

        Term initialConfiguration = executionContext.getInitialConfiguration();
        Context context = executionContext.getContext();
        ConsoleReader reader;
        try {
            reader = new ConsoleReader();
        } catch (IOException e) {
            if (context.globalOptions.debug) {
                e.printStackTrace();
            }
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL,
                    "IO error detected interacting with console"));
            return false;
        }
        try {
            // adding autocompletion and history feature to the stepper internal
            // commandline by using the JLine library
            reader.setBellEnabled(false);

            List<Completor> argCompletor = new LinkedList<Completor>();
            argCompletor.add(new SimpleCompletor(new String[] { "help",
                    "exit", "resume", "step", "search", "select",
                    "show-graph", "show-state", "show-transition", "save", "load", "read" }));
            argCompletor.add(new FileNameCompletor());
            List<Completor> completors = new LinkedList<Completor>();
            completors.add(new ArgumentCompletor(argCompletor));
            reader.addCompletor(new MultiCompletor(completors));

            KRun krun = obtainKRun(context);
            krun.setBackendOption("io", false);
            KRunDebugger debugger;
            try {
                if (state == null) {
                    debugger = krun.debug(initialConfiguration);
                    System.out
                            .println("After running one step of execution the result is:");
                    System.out.println(debugger.printState(debugger.getCurrentState()));
                } else {
                    debugger = krun.debug(state.getResult().getGraph());
                }
            } catch (UnsupportedBackendOptionException e) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                        "Backend \"" + context.kompileOptions.backend.name().toLowerCase()
                        + "\" does not support option " + e.getMessage()));
                return false; //unreachable
            }
            while (true) {
                System.out.println();
                String input;
                try {
                    input = reader.readLine("Command > ");
                } catch (IOException e) {
                    if (context.globalOptions.debug) {
                        e.printStackTrace();
                    }
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL,
                            "IO error detected interacting with console"));
                    return false;
                }
                if (input == null) {
                    // probably pressed ^D
                    System.out.println();
                    return true;
                }
                if (input.equals("")) {
                    continue;
                }

                KRunDebuggerOptions options = new KRunDebuggerOptions();
                JCommander jc = new JCommander(options);
                jc.addCommand(options.help);
                jc.addCommand(options.step);
                jc.addCommand(options.search);
                jc.addCommand(options.select);
                jc.addCommand(options.showGraph);
                jc.addCommand(options.showState);
                jc.addCommand(options.showTransition);
                jc.addCommand(options.resume);
                jc.addCommand(options.exit);
                jc.addCommand(options.save);
                jc.addCommand(options.load);
                jc.addCommand(options.read);

                try {
                    jc.parse(input.split("\\s+"));

                    if (jc.getParsedCommand().equals("help")) {
                        if (options.help.command == null || options.help.command.size() == 0) {
                            jc.usage();
                        } else {
                            for (String command : options.help.command) {
                                if (jc.getCommands().containsKey(command)) {
                                    jc.usage(command);
                                }
                            }
                        }
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandExit) {
                        return true;
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandResume) {
                        debugger.resume();
                        System.out.println(debugger.printState(debugger.getCurrentState()));
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandStep) {
                        debugger.step(options.step.numSteps);
                        System.out.println(debugger.printState(debugger.getCurrentState()));
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandSearch) {
                        SearchResults states = debugger.stepAll(options.search.numSteps);
                        System.out.println(states);
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandSelect) {
                        debugger.setCurrentState(options.select.stateId);
                        System.out.println(debugger.printState(debugger.getCurrentState()));
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowGraph) {
                        System.out.println("\nThe search graph is:\n");
                        System.out.println(debugger.getGraph());
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowState) {
                        System.out.println(debugger.printState(options.showState.stateId));
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowTransition) {
                        int state1 = options.showTransition.state1();
                        int state2 = options.showTransition.state2();
                        System.out.println(debugger.printEdge(state1, state2));
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandSave) {
                        BinaryLoader.saveOrDie(options.save.file.getAbsolutePath(), debugger.getGraph());
                        System.out.println("File successfully saved.");
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandLoad) {
                        DirectedGraph<KRunState, Transition> savedGraph =
                                BinaryLoader.loadOrDie(DirectedGraph.class, options.load.file.getAbsolutePath());
                        debugger = krun.debug(savedGraph);
                        debugger.setCurrentState(1);
                        System.out.println("File successfully loaded.");
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandRead) {
                        debugger.readFromStdin(StringBuiltin.valueOf(options.read.string).stringValue());
                        System.out.println(debugger.printState(debugger.getCurrentState()));
                    } else {
                        assert false : "Unexpected krun debugger command " + jc.getParsedCommand();
                    }
                } catch (ParameterException e) {
                    System.err.println(e.getMessage());
                    jc.usage();
                } catch (IllegalArgumentException | IllegalStateException e) {
                    System.err.println(e.getMessage());
                }
            }
        } catch (KRunExecutionException e) {
            if (context.globalOptions.debug) {
                e.printStackTrace();
            }
            new RunProcess().printError(e.getMessage());
            return false;
        }
    }

    private static boolean guiDebugExecution(ExecutionContext executionContext) {
        Term initialConfiguration = executionContext.getInitialConfiguration();
        Context context = executionContext.getContext();
        try {
            KRun krun = obtainKRun(context);
            krun.setBackendOption("io", false);
            RunKRunCommand cmd = new RunKRunCommand(initialConfiguration, krun, context);
            MainWindow window = new MainWindow(cmd);
            synchronized(window.lock) {
                while (true) {
                    try {
                        window.lock.wait();
                        return true;
                    } catch (InterruptedException e) {
                        //keep waiting
                    }
                }
            }
        } catch (KRunExecutionException e) {
            if (context.globalOptions.debug) {
                e.printStackTrace();
            }
            new RunProcess().printError(e.getMessage());
            return false;
        }
    }

    /**
     * @param cmds represents the arguments/options given to krun command..
     * @return true if the application completed normally; false otherwise
     */
    public static boolean execute_Krun(String[] cmds) {
        KRunOptions options = new KRunOptions();
        options.global.initialize();
        try {
            JCommander jc = new JCommander(options, cmds);
            jc.setProgramName("krun");
            jc.setParameterDescriptionComparator(new SortedParameterDescriptions(KRunOptions.Experimental.class, SMTOptions.class, JavaExecutionOptions.class));

            if (options.experimental.debuggerGui()) {
                System.setProperty("java.awt.headless", "false");
            }

            if (options.global.help) {
                StringBuilder sb = new StringBuilder();
                jc.usage(sb);
                System.out.print(StringUtil.finesseJCommanderUsage(sb.toString(), jc)[0]);
                return true;
            }

            if (options.helpExperimental) {
                StringBuilder sb = new StringBuilder();
                jc.usage(sb);
                System.out.print(StringUtil.finesseJCommanderUsage(sb.toString(), jc)[1]);
                return true;
            }

            if (options.global.version) {
                String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
                System.out.print(msg);
                return true;
            }

            sw.printIntermediate("Deleting temporary krun directory");

            ExecutionContext mainExecutionContext = new ExecutionContext(options, options.configurationCreation, sw);

            // Parse the program arguments

            if(options.experimental.simulation != null) {
                ConfigurationCreationOptions simulationCCOptions = new ConfigurationCreationOptions();
                new JCommander(simulationCCOptions,
                        options.experimental.simulation.toArray(
                                new String[options.experimental.simulation.size()]));

                ExecutionContext simulationExecutionContext = new ExecutionContext(options, simulationCCOptions, sw);

                Term leftInitTerm = mainExecutionContext.getInitialConfiguration();
                Term rightInitTerm = simulationExecutionContext.getInitialConfiguration();
                Context contextLeft = mainExecutionContext.getContext();
                Context contextRight = mainExecutionContext.getContext();

                Waitor runSimulation;
                try {
                    runSimulation = new Waitor(contextLeft, contextRight, leftInitTerm, rightInitTerm);
                } catch (KRunExecutionException e) {
                    if (options.global.debug) {
                        e.printStackTrace();
                    }
                    new RunProcess().printError(e.getMessage());
                    return false;
                }

                runSimulation.start();

                try {
                    runSimulation.join();
                } catch (InterruptedException e) {
                    return false;
                }
                return true;
            }

            if (!options.experimental.debugger() && !options.experimental.debuggerGui()) {
                normalExecution(mainExecutionContext);
            } else {
                if (options.experimental.debuggerGui())
                    return guiDebugExecution(mainExecutionContext);
                else
                    debugExecution(mainExecutionContext, null);
            }
            return true;
        } catch (ParameterException ex) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, ex.getMessage()));
            return false;
        }
    }
}

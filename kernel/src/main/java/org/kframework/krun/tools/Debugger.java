// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.tools;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import jline.ArgumentCompletor;
import jline.Completor;
import jline.ConsoleReader;
import jline.FileNameCompletor;
import jline.MultiCompletor;
import jline.SimpleCompletor;

import org.kframework.backend.unparser.PrintTransition;
import org.kframework.kil.Attributes;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunDebuggerOptions;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.Transition;
import org.kframework.krun.api.UnsupportedBackendOptionException;
import org.kframework.transformation.Transformation;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.InjectGeneric;
import org.kframework.utils.inject.Main;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import com.google.inject.Inject;
import com.sun.org.apache.xerces.internal.impl.dv.util.Base64;

public interface Debugger {

    /**
    Get the current graph of the explored state space in the transition system.
    @return A graph whose nodes and edges describe the explored state of the program.
    */
    public abstract KRunGraph getGraph();

    /**
     * Reset the debugger's configuration to the graph specified by the parameter
     */
    public abstract void setGraph(KRunGraph graph);

    /**
    Get the state number of the currently selected state.
    @return An unique integer identifying the currently selected state; null if no state is selected
    */
    public abstract Integer getCurrentState();

    /**
    Set the selected state of the debugger.
    @param stateNum An integer uniquely identifying the state to select; null to deselect current
    state.
    @exception IllegalArgumentException Thrown if the specified state is not a valid state in the
    graph (or null)
    */
    public abstract void setCurrentState(Integer stateNum);

    /**
    Get a state by its state number.
    @param stateNum An integer uniquely identifying the state to select
    @return The node in the explored state graph with the specified state number.
    @exception IllegalArgumentException Thrown if the state number is not in the graph
    */
    public abstract KRunState getState(int stateNum);

    /**
    Get the edge connecting two states.
    @param state1 The integral state number of the origin state of the edge.
    @param state2 The integral state number of the destination state of the edge.
    @exception IllegalArgumentException Thrown if no edge connects state1 and state2
    @return Information concerning the transition in the transition system which connected state1 to
    state2
    */
    public abstract Transition getEdge(int state1, int state2);

    /**
    Step a particular number of transitions. This function returns when the specified number of
    steps have been taken, or when rewriting has terminated.
    @param steps The maximum number of transitions to follow through (0 to stop before first
    transition)
    */
    public abstract void step(int steps) throws KRunExecutionException;

    /**
    Explore the complete search graph from the currently selected state forward a specified number
    of steps.
    @param steps The maximum depth of the search to perform.
    @return A set of all new states discovered by the stepper after searching the specified number
    of steps.
    */
    public abstract SearchResults stepAll(int steps) throws KRunExecutionException;

    /**
    Explore the search graph one step at a time until rewriting terminates.
    */
    public abstract void resume() throws KRunExecutionException;

    /**
    Read a string and append it to the buffer for stdin.
    @param s The string to append to stdin.
    */
    public abstract void readFromStdin(String s);

    /**
     * Start debugging from a particular term
     */
    public abstract void start(Term initialConfiguration) throws KRunExecutionException;

    public static class Tool implements Transformation<Void, Void> {

        private final KExceptionManager kem;
        private final Term initialConfiguration;
        private final KompileOptions kompileOptions;
        private final BinaryLoader loader;
        @InjectGeneric private Transformation<KRunState, String> statePrinter;
        @InjectGeneric private Transformation<SearchResults, String> searchPrinter;
        @InjectGeneric private Transformation<KRunGraph, String> graphPrinter;
        @InjectGeneric private Transformation<Transition, String> transitionPrinter;
        private final Debugger debugger;
        private final Context context;
        private final FileUtil files;

        @Inject
        Tool(
                KExceptionManager kem,
                @Main Term initialConfiguration,
                @Main KompileOptions kompileOptions,
                BinaryLoader loader,
                @Main Debugger debugger,
                @Main Context context,
                @Main FileUtil files) {
            this.kem = kem;
            this.initialConfiguration = initialConfiguration;
            this.kompileOptions = kompileOptions;
            this.loader = loader;
            this.debugger = debugger;
            this.context = context;
            this.files = files;
        }

        Tool(
                KExceptionManager kem,
                @Main Term initialConfiguration,
                @Main KompileOptions kompileOptions,
                BinaryLoader loader,
                Transformation<KRunState, String> statePrinter,
                Transformation<SearchResults, String> searchPrinter,
                Transformation<KRunGraph, String> graphPrinter,
                Transformation<Transition, String> transitionPrinter,
                @Main Debugger debugger,
                @Main Context context,
                @Main FileUtil files) {
            this(kem, initialConfiguration, kompileOptions, loader, debugger, context, files);
            this.statePrinter = statePrinter;
            this.searchPrinter = searchPrinter;
            this.graphPrinter = graphPrinter;
            this.transitionPrinter = transitionPrinter;
        }

        private static Object command(JCommander jc) {
            return jc.getCommands().get(jc.getParsedCommand()).getObjects().get(0);
        }

        @Override
        public Void run(Void v, Attributes a) {
            a.add(Context.class, context);
            ConsoleReader reader;
            try {
                reader = new ConsoleReader();
            } catch (IOException e) {
                throw KExceptionManager.internalError("IO error detected interacting with console", e);
            }
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

            try {
                debugger.start(initialConfiguration);
                System.out.println("After running one step of execution the result is:\n");
                System.out.println(statePrinter.run(debugger.getState(debugger.getCurrentState()), a));
            } catch (UnsupportedBackendOptionException e) {
                throw KExceptionManager.criticalError("Backend \""
                        + kompileOptions.backend
                        + "\" does not support option " + e.getMessage(), e);
            } catch (KRunExecutionException e) {
                throw KExceptionManager.criticalError(e.getMessage(), e);
            }
            while (true) {
                System.out.println();
                String input;
                try {
                    input = reader.readLine("Command > ");
                } catch (IOException e) {
                    throw KExceptionManager.internalError("IO error detected interacting with console", e);
                }
                if (input == null) {
                    // probably pressed ^D
                    System.out.println();
                    return null;
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
                        return null;

                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandResume) {
                        debugger.resume();
                        System.out.println(statePrinter.run(debugger.getState(debugger.getCurrentState()), a));

                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandStep) {
                        debugger.step(options.step.numSteps);
                        System.out.println(statePrinter.run(debugger.getState(debugger.getCurrentState()), a));

                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandSearch) {
                        SearchResults states = debugger.stepAll(options.search.numSteps);
                        System.out.println(searchPrinter.run(states, a));

                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandSelect) {
                        debugger.setCurrentState(options.select.stateId);
                        System.out.println(statePrinter.run(debugger.getState(debugger.getCurrentState()), a));

                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowGraph) {
                        System.out.println("\nThe search graph is:\n");
                        System.out.println(graphPrinter.run(debugger.getGraph(), a));

                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowState) {
                        System.out.println(statePrinter.run(debugger.getState(options.showState.stateId), a));

                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowTransition) {
                        int state1 = options.showTransition.state1();
                        int state2 = options.showTransition.state2();
                        a.add(KRunGraph.class, debugger.getGraph());
                        a.add(Boolean.class, PrintTransition.PRINT_VERBOSE_GRAPH, true);
                        System.out.println(transitionPrinter.run(debugger.getEdge(state1, state2), a));
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandSave) {
                        try (ByteArrayOutputStream out = new ByteArrayOutputStream()) {
                            loader.saveOrDie(out, debugger.getGraph());
                            files.saveToWorkingDirectory(options.save.file, Base64.encode(out.toByteArray()));
                        } catch (IOException e) {
                            throw KExceptionManager.internalError("Error writing to binary file", e);
                        }
                        System.out.println("File successfully saved.");
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandLoad) {
                        KRunGraph savedGraph;
                        try (ByteArrayInputStream in = new ByteArrayInputStream(
                                Base64.decode(files.loadFromWorkingDirectory(options.load.file)))) {
                            savedGraph = loader.loadOrDie(KRunGraph.class, in);
                            debugger.setGraph(savedGraph);
                            debugger.setCurrentState(0);
                            System.out.println("File successfully loaded.");
                        } catch (IOException e) {
                            throw KExceptionManager.internalError("Error reading from binary file", e);
                        }
                    } else if (command(jc) instanceof KRunDebuggerOptions.CommandRead) {
                        debugger.readFromStdin(StringBuiltin.valueOf(options.read.string).stringValue());
                        System.out.println(statePrinter.run(debugger.getState(debugger.getCurrentState()), a));
                    } else {
                        assert false : "Unexpected krun debugger command " + jc.getParsedCommand();
                    }
                } catch (ParameterException e) {
                    System.err.println(e.getMessage());
                    jc.usage();
                } catch (IllegalArgumentException | IllegalStateException e) {
                    System.err.println(e.getMessage());
                } catch (KRunExecutionException e) {
                    System.err.println("Error executing krun: " + e.getMessage());
                }
            }
        }

        @Override
        public String getName() {
            return "--debugger";
        }
    }

}

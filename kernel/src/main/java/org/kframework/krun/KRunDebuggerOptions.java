// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import java.util.List;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;

public final class KRunDebuggerOptions {

    public final CommandHelp help = new CommandHelp();
    public final CommandStep step = new CommandStep();
    public final CommandSearch search = new CommandSearch();
    public final CommandSelect select = new CommandSelect();
    public final CommandShowGraph showGraph = new CommandShowGraph();
    public final CommandShowState showState = new CommandShowState();
    public final CommandShowTransition showTransition = new CommandShowTransition();
    public final CommandResume resume = new CommandResume();
    public final CommandExit exit = new CommandExit();
    public final CommandSave save = new CommandSave();
    public final CommandLoad load = new CommandLoad();
    public final CommandRead read = new CommandRead();

    @Parameters(commandNames="help", commandDescription="Display help on the available commands")
    public static final class CommandHelp {

        @Parameter(description="<command>")
        public List<String> command;
    }

    @Parameters(commandNames="step", commandDescription="Execute one or more steps from the current state")
    public static final class CommandStep {

        @Parameter(names="-s", description="Number of steps to step")
        public int numSteps = 1;
    }

    @Parameters(commandNames={"search", "step-all"}, commandDescription="Search one or more steps from the current state")
    public static final class CommandSearch {

        @Parameter(names="-s", description="Number of steps to step")
        public int numSteps = 1;
    }

    @Parameters(commandNames="select", commandDescription="Select a particular state as the current state")
    public static final class CommandSelect {

        @Parameter(names="-s", description="State ID to select", required=true)
        public int stateId;
    }

    @Parameters(commandNames={"show-graph", "show-search-graph"}, commandDescription="Displays the search graph of states in the execution trace")
    public static final class CommandShowGraph {}

    @Parameters(commandNames={"show-state", "show-node"}, commandDescription="Displays info about the specified state in the search graph")
    public static final class CommandShowState {

        @Parameter(names="-s", description="State ID to show", required=true)
        public int stateId;
    }

    @Parameters(commandNames={"show-transition", "show-edge"}, commandDescription="Displays info about the specified transition in the search graph")
    public static final class CommandShowTransition {

        @Parameter(names="-s", description="<state 1> <state 2>", required=true, arity=2)
        public List<Integer> states;

        public int state1() {
            return states.get(0);
        }

        public int state2() {
            return states.get(1);
        }
    }

    @Parameters(commandNames={"resume", "run"}, commandDescription="Resume stepping the execution until it terminates")
    public static final class CommandResume {}

    @Parameters(commandNames={"exit", "abort", "quit"}, commandDescription="Abort the execution and exit from the debug mode")
    public static final class CommandExit {}

    @Parameters(commandNames="save", commandDescription="Save the debug session to a file")
    public static final class CommandSave {

        @Parameter(names="-f", description="File to save to", required=true)
        public String file;
    }

    @Parameters(commandNames="load", commandDescription="Load the debug session from a file")
    public static final class CommandLoad {

        @Parameter(names="-f", description="File to load from", required=true)
        public String file;
    }

    @Parameters(commandNames="read", commandDescription="Emulate reading a string from stdin")
    public static final class CommandRead {

        @Parameter(names="-s", description="String to read")
        public String string;
    }
}

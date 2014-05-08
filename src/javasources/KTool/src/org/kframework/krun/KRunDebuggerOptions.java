// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.io.File;
import java.util.List;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
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
        
        @Parameter(description="<num steps>")
        public int numSteps = 1;
    }
    
    @Parameters(commandNames={"search", "step-all"}, commandDescription="Search one or more steps from the current state")
    public static final class CommandSearch {
        
        @Parameter(description="<num steps>")
        public int numSteps = 1;
    }
    
    @Parameters(commandNames="select", commandDescription="Select a particular state as the current state")
    public static final class CommandSelect {
        
        @Parameter(description="<state id>", required=true)
        public int stateId;
    }
    
    @Parameters(commandNames={"show-graph", "show-search-graph"}, commandDescription="Displays the search graph of states in the execution trace")
    public static final class CommandShowGraph {}
    
    @Parameters(commandNames={"show-state", "show-node"}, commandDescription="Displays info about the specified state in the search graph")
    public static final class CommandShowState {
        
        @Parameter(description="<state id>", required=true)
        public int stateId;
    }
    
    @Parameters(commandNames={"show-transition", "show-edge"}, commandDescription="Displays info about the specified transition in the search graph")
    public static final class CommandShowTransition {
        
        @Parameter(description="<state 1> <state 2>", required=true, arity=2)
        public List<String> states;
        
        public int state1() {
            try {
                return Integer.parseInt(states.get(0));
            } catch (NumberFormatException e) {
                throw new ParameterException(e.getMessage());
            }
        }
        
        public int state2() {
            try {
                return Integer.parseInt(states.get(1));
            } catch (NumberFormatException e) {
                throw new ParameterException(e.getMessage());
            }
        }
    }
    
    @Parameters(commandNames={"resume", "run"}, commandDescription="Resume stepping the execution until it terminates")
    public static final class CommandResume {}
    
    @Parameters(commandNames={"exit", "abort", "quit"}, commandDescription="Abort the execution and exit from the debug mode")
    public static final class CommandExit {}
    
    @Parameters(commandNames="save", commandDescription="Save the debug session to a file")
    public static final class CommandSave {
        
        @Parameter(description="<file>", required=true)
        public File file;
    }
    
    @Parameters(commandNames="load", commandDescription="Load the debug session from a file")
    public static final class CommandLoad {
        
        @Parameter(description="<file>", required=true)
        public File file;
    }
    
    @Parameters(commandNames="read", commandDescription="Emulate reading a string from stdin")
    public static final class CommandRead {
        
        @Parameter(description="<string>")
        public String string;
    }
}

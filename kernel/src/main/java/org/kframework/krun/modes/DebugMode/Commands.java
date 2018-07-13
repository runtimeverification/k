// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.krun.modes.DebugMode;

import org.kframework.debugger.DebuggerMatchResult;
import org.kframework.debugger.DebuggerState;
import org.kframework.debugger.KDebug;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.krun.KRun;
import org.kframework.unparser.ColorSetting;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.OutputModes;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;
import java.util.List;
import java.util.Optional;

import static org.kframework.krun.KRun.*;

/**
 * Created by Manasvi on 7/22/15.
 * <p>
 * Classes concerned with TUI commands go under this class.
 * Commands must implement {@link org.kframework.krun.modes.DebugMode.Command}.
 */
public class Commands {

    public static class StepCommand implements Command {

        private int stepCount;

        public StepCommand(int stepCount) {
            this.stepCount = stepCount;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            CommandUtils utils = new CommandUtils(isSource);
            int activeStateId = session.getActiveStateId();
            DebuggerState prevState = session.getStates().get(activeStateId);
            DebuggerState steppedState = session.step(activeStateId, stepCount);
            int effectiveStepCount = steppedState.getStepNum() - prevState.getStepNum();
            if (effectiveStepCount < stepCount) {
                utils.print("Attempted " + stepCount + " step(s). " + "Took " + effectiveStepCount + " steps(s).");
                utils.print("Final State Reached");
                utils.displayWatches(session.files(), steppedState.getWatchList(), compiledDefinition);
                return;
            }
            utils.print(stepCount + " Step(s) Taken.");
            utils.displayWatches(session.files(), steppedState.getWatchList(), compiledDefinition);
        }
    }

    public static class WatchCommand implements Command {
        private Optional<String> pattern;

        public WatchCommand(Optional<String> pattern) {
            this.pattern = pattern;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            CommandUtils utils = new CommandUtils(isSource);
            pattern.ifPresent(pattern -> {
                if (isSource) {
                    session.addWatch(pattern, "<Source File>");
                } else {
                    session.addWatch(pattern, "<Command Line>");
                }
            });
            utils.displayWatches(
                    session.files(),
                    session.getActiveState().getWatchList(),
                    compiledDefinition
            );
        }
    }

    public static class PeekCommand implements Command {

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            CommandUtils utils = new CommandUtils(isSource);
            DebuggerState requestedState = session.getActiveState();
            if (requestedState != null) {
                KPrint.prettyPrint(compiledDefinition.getParsedDefinition(), compiledDefinition.languageParsingModule(), session.files(), compiledDefinition.kompileOptions, OutputModes.PRETTY, s -> utils.print(s), requestedState.getCurrentK(), ColorSetting.ON);
            } else {
                throw KEMException.debuggerError("\"Requested State/Configuration Unreachable\",");
            }
        }
    }

    public static class BackStepCommand implements Command {

        private int backStepCount;

        public BackStepCommand(int backStepCount) {
            this.backStepCount = backStepCount;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            int activeConfigurationId = session.getActiveState().getStepNum();
            CommandUtils utils = new CommandUtils(isSource);
            if (backStepCount > 1 && (backStepCount) > activeConfigurationId) {
                throw KEMException.debuggerError("Number of Configuration(s) is " + (activeConfigurationId + 1) + ". Step Count to go back must be in range [0, " + (activeConfigurationId + 1) + ")");

            }
            DebuggerState backSteppedState = session.backStep(session.getActiveStateId(), backStepCount);
            if (backSteppedState == null) {
                throw KEMException.debuggerError("\"Already at Start State, Cannot take steps.\",");
            }
            utils.print("Took -" + backStepCount + " step(s)");
            utils.displayWatches(session.files(), backSteppedState.getWatchList(), compiledDefinition);
        }
    }

    public static class SelectCommand implements Command {
        private int stateNum;

        public SelectCommand(int stepNum) {
            this.stateNum = stepNum;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            DebuggerState selectedState = session.setState(stateNum);
            if (selectedState == null) {
                throw KEMException.debuggerError("Requested State not Present in List of states");
            }
            CommandUtils utils = new CommandUtils(isSource);
            utils.print("Selected State " + stateNum);
        }
    }

    public static class JumpToCommand implements Command {

        private Optional<Integer> stateNum;

        private Optional<Integer> configurationNum;

        public JumpToCommand(Optional<Integer> stateNum, Optional<Integer> configurationNum) {
            this.stateNum = stateNum;
            this.configurationNum = configurationNum;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            int requestedState = stateNum.orElse(session.getActiveStateId());
            CommandUtils utils = new CommandUtils(isSource);
            DebuggerState nextState = session.setState(requestedState);
            if (nextState == null) {
                throw KEMException.debuggerError("State Number specified does not exist");
            } else if (!configurationNum.isPresent()) {
                utils.print("Selected State " + requestedState);
            } else {
                int requestedConfig = configurationNum.get();
                DebuggerState finalState = session.jumpTo(requestedState, requestedConfig);
                if (finalState == null) {
                    throw KEMException.debuggerError("Requested Step Number couldn't be selected.");
                } else if (!stateNum.isPresent()) {
                    utils.print("Jumped to Step Number " + requestedConfig);
                } else {
                    utils.print("Jumped to State Number " + requestedState + " and Step Number " + requestedConfig);
                }
                utils.displayWatches(session.files(), finalState.getWatchList(), compiledDefinition);
                return;
            }
            utils.displayWatches(session.files(), nextState.getWatchList(), compiledDefinition);
        }

    }

    public static class QuitCommand implements Command {

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            return;
        }
    }

    public static class ResumeCommand implements Command {
        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            DebuggerState currentState = session.getStates().get(session.getActiveStateId());
            DebuggerState finalState = session.resume();
            CommandUtils utils = new CommandUtils(isSource);
            utils.print("Took " + (finalState.getStepNum() - currentState.getStepNum()) + " step(s)");
            utils.displayWatches(session.files(), finalState.getWatchList(), compiledDefinition);
        }
    }

    public static class CheckpointCommand implements Command {
        private int checkpointInterval;

        public CheckpointCommand(int checkpointInterval) {
            this.checkpointInterval = checkpointInterval;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            CommandUtils utils = new CommandUtils(isSource);
            if (checkpointInterval <= 0) {
                throw KEMException.debuggerError("Checkpoint Value must be >= 1");
            }
            session.setCheckpointInterval(checkpointInterval);
            utils.print("Checkpointing Interval set to " + checkpointInterval);
            return;
        }
    }


    public static class ShowCommand implements Command {
        private String pattern;

        public ShowCommand(String pattern) {
            this.pattern = pattern;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            DebuggerMatchResult result = session.match(pattern, "<Command Line>");
            CommandUtils utils = new CommandUtils(isSource);
            utils.prettyPrintSubstitution(session.files(), result, compiledDefinition);
        }

    }

    public static class SourceCommand implements Command {
        private String sourceFile;

        public SourceCommand(String sourceFile) {
            this.sourceFile = sourceFile;
        }

        public String getSourceFile() {
            return sourceFile;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            return;
        }
    }

    public static class RemoveWatchCommand implements Command {
        private int watchNum;

        public RemoveWatchCommand(int watchNum) {
            this.watchNum = watchNum;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            if (session.removeWatch(watchNum) < 0) {
                throw KEMException.debuggerError("Watch Doesn't Exists");
            }
            CommandUtils utils = new CommandUtils(isSource);
            utils.print("Watch " + (watchNum) + " removed");
        }
    }

    public static class CopyCommand implements Command {
        private int stateNum;

        public CopyCommand(int stateNum) {
            this.stateNum = stateNum;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            if (session.createCopy(stateNum) == null) {
                throw KEMException.debuggerError("StateNumber Speicified doesn't exist");
            }
            CommandUtils utils = new CommandUtils(isSource);
            utils.print("Copied State " + stateNum);
        }
    }

    public static class GetStatesCommand implements Command {
        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean isSource) {
            List<DebuggerState> stateList = session.getStates();
            int activeStateIndex = session.getActiveStateId();
            int i = 0;
            CommandUtils utils = new CommandUtils(isSource);
            for (DebuggerState state : stateList) {
                if (i == activeStateIndex) {
                    utils.print("State " + (i++) + "*");
                } else {
                    utils.print("State " + (i++));
                }
                utils.print("Step Count " + state.getStepNum());
            }
        }
    }

    private static class CommandUtils {
        private boolean disableOutput;

        private CommandUtils(boolean isSource) {
            this.disableOutput = isSource;
        }

        private void prettyPrintSubstitution(FileUtil files, DebuggerMatchResult result, CompiledDefinition compiledDefinition) {
            if (disableOutput) {
                return;
            }
            KPrint.prettyPrint(compiledDefinition.getParsedDefinition(), compiledDefinition.languageParsingModule(), files, compiledDefinition.kompileOptions, OutputModes.PRETTY, s -> System.out.println(s), result.getSubstitutions(), ColorSetting.ON);
        }

        private void print(byte[] bytes){
            if (!disableOutput) {
                try {
                    System.out.write(bytes);
                } catch (IOException e) {
                    throw KEMException.debuggerError("IOError :" + e.getMessage());
                }
            }
        }

        private void print(String printString) {
            if (!disableOutput) {
                System.out.println(printString);
            }
        }

        private void displayWatches(FileUtil files, List<DebuggerMatchResult> watches, CompiledDefinition compiledDefinition) {
            if (watches.isEmpty()) {
                return;
            }
            print("Watches:");
            int i = 0;
            for (DebuggerMatchResult watch : watches) {
                print("Watch " + (i));
                print("Pattern : " + watch.getPattern());
                prettyPrintSubstitution(files, watch, compiledDefinition);
                i++;
            }
        }
    }
}

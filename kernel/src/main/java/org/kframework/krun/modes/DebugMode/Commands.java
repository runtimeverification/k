// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes.DebugMode;

import org.kframework.backend.unparser.OutputModes;
import org.kframework.debugger.DebuggerMatchResult;
import org.kframework.debugger.DebuggerState;
import org.kframework.debugger.KDebug;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.kore.compile.VisitKORE;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Consumer;

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
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            CommandUtils utils = new CommandUtils(disableOutput);
            int activeStateId = session.getActiveStateId();
            DebuggerState prevState = session.getStates().get(activeStateId);
            DebuggerState steppedState = session.step(activeStateId, stepCount);
            int effectiveStepCount = steppedState.getStepNum() - prevState.getStepNum();
            if (effectiveStepCount < stepCount) {
                utils.print("Attempted " + stepCount + " step(s). " + "Took " + effectiveStepCount + " steps(s).",
                        s -> System.out.println(s));
                utils.print("Final State Reached", s -> System.out.println(s));
                return;
            }
            utils.print(stepCount + " Step(s) Taken.", s -> System.out.println(s));
            utils.displayWatches(steppedState.getWatchList(), compiledDefinition);
        }
    }

    public static class WatchCommand implements Command {
        private Optional<String> pattern;

        public WatchCommand(Optional<String> pattern) {
            this.pattern = pattern;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            CommandUtils utils = new CommandUtils(disableOutput);
            pattern.ifPresent(pattern -> {
                session.addWatch(pattern);
            });
            utils.displayWatches(
                    session.getActiveState().getWatchList(),
                    compiledDefinition
            );
        }
    }

    public static class PeekCommand implements Command {

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            CommandUtils utils = new CommandUtils(disableOutput);
            DebuggerState requestedState = session.getActiveState();
            if (requestedState != null) {
                prettyPrint(compiledDefinition, OutputModes.PRETTY, s -> utils.print(s, y -> System.out.println(y)), requestedState.getCurrentK());
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
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            int activeConfigurationId = session.getActiveState().getStepNum();
            CommandUtils utils = new CommandUtils(disableOutput);
            if ((backStepCount - 1) > activeConfigurationId) {
                throw KEMException.debuggerError("Number of Configuration(s) is " + (activeConfigurationId + 1) + ". Step Count to go back must be in range [0, " + (activeConfigurationId + 1) + ")");

            }
            DebuggerState backSteppedState = session.backStep(session.getActiveStateId(), backStepCount);
            if (backSteppedState == null) {
                throw KEMException.debuggerError("\"Already at Start State, Cannot take steps.\",");
            }
            utils.print("Took -" + backStepCount + " step(s)", s -> System.out.println(s));
            utils.displayWatches(backSteppedState.getWatchList(), compiledDefinition);
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
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            int requestedState = stateNum.orElse(session.getActiveStateId());
            CommandUtils utils = new CommandUtils(disableOutput);
            DebuggerState nextState = session.setState(requestedState);
            if (nextState == null) {
                throw KEMException.debuggerError("State Number specified does not exist\"");
            } else if (!configurationNum.isPresent()) {
                utils.print("Selected State " + requestedState, s -> System.out.println(s));
            } else {
                int requestedConfig = configurationNum.get();
                DebuggerState finalState = session.jumpTo(requestedState, requestedConfig);
                if (finalState == null) {
                    throw KEMException.debuggerError("Requested Step Number couldn't be selected.");
                } else if (!stateNum.isPresent()) {
                    utils.print("Jumped to Step Number " + requestedConfig, s -> System.out.println(s));
                } else {
                    utils.print("Jumped to State Number " + requestedState + " and Step Number " + requestedConfig,
                            x -> System.out.println(x));
                }
                utils.displayWatches(finalState.getWatchList(), compiledDefinition);
                return;
            }
            utils.displayWatches(nextState.getWatchList(), compiledDefinition);
        }

    }

    public static class QuitCommand implements Command {

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            return;
        }
    }

    public static class ResumeCommand implements Command {
        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            DebuggerState currentState = session.getStates().get(session.getActiveStateId());
            DebuggerState finalState = session.resume();
            CommandUtils utils = new CommandUtils(disableOutput);
            utils.print(finalState.getStepNum() - currentState.getStepNum() + "Step(s) Taken", s -> System.out.println(s));
            utils.displayWatches(finalState.getWatchList(), compiledDefinition);
        }
    }

    public static class CheckpointCommand implements Command {
        private int checkpointInterval;

        public CheckpointCommand(int checkpointInterval) {
            this.checkpointInterval = checkpointInterval;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            CommandUtils utils = new CommandUtils(disableOutput);
            if (checkpointInterval <= 0) {
                KEMException.debuggerError("Checkpoint Value must be >= 1");
            }
            session.setCheckpointInterval(checkpointInterval);
            utils.print("Checkpointing Interval set to " + checkpointInterval, s -> System.out.println(s));
            return;
        }
    }


    public static class ShowCommand implements Command {
        private String pattern;

        public ShowCommand(String pattern) {
            this.pattern = pattern;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            DebuggerMatchResult result = session.match(pattern);
            CommandUtils utils = new CommandUtils(disableOutput);
            utils.prettyPrintSubstitution(result, compiledDefinition);
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
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            return;
        }
    }

    public static class RemoveWatchCommand implements Command {
        private int watchNum;

        public RemoveWatchCommand(int watchNum) {
            this.watchNum = watchNum;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            if (session.removeWatch(watchNum) < 0) {
                throw KEMException.debuggerError("Watch Doesn't Exists");
            }
            CommandUtils utils = new CommandUtils(disableOutput);
            utils.print("Watch " + (watchNum + 1) + "removed", x -> System.out.println(x));
        }
    }

    public static class CopyCommand implements Command {
        private int stateNum;

        public CopyCommand(int stateNum) {
            this.stateNum = stateNum;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput) {
            if (session.createCopy(stateNum) == null) {
                throw KEMException.debuggerError("StateNumber Speicified doesn't exist");
            }
            CommandUtils utils = new CommandUtils(disableOutput);
            utils.print("Selected State " + stateNum, s -> System.out.println(s));
        }
    }

    private static class CommandUtils {
        private boolean disableOutput;

        private CommandUtils(boolean disableOutput) {
            this.disableOutput = disableOutput;
        }

        private void prettyPrintSubstitution(DebuggerMatchResult result, CompiledDefinition compiledDefinition) {
            List<? extends Map<? extends KVariable, ? extends K>> substList = result.getSubstitutions();

            if (substList.isEmpty()) {
                System.out.println("No Substitution Found");
                return;
            }

            List<String> varList = new ArrayList<>();
            new VisitKORE() {
                @Override
                public Void apply(KVariable k) {
                    /* Not Observing reflexivity Rule requires comparison by name */
                    varList.add(k.name());
                    return super.apply(k);
                }
            }.apply(result.getParsedRule().body());

            substList.stream()
                    .forEach(map ->
                            map.entrySet()
                                    .stream()
                                    .filter(x -> varList.contains(x.getKey().name()))
                                    .forEach(x -> {
                                        prettyPrint(compiledDefinition, OutputModes.PRETTY, s -> print(s, cons -> System.out.print(cons)), x.getKey());
                                        print(" ----> ", cons -> System.out.print(cons));
                                        prettyPrint(compiledDefinition, OutputModes.PRETTY, s -> print(s, cons -> System.out.println(cons)), x.getValue());
                                    }));


        }

        private void print(String printString, Consumer<String> printer) {
            if (!disableOutput) {
                printer.accept(printString);
            }
        }

        private void displayWatches(List<DebuggerMatchResult> watches, CompiledDefinition compiledDefinition) {
            if (watches.isEmpty()) {
                return;
            }
            print("Watches:", x -> System.out.println(x));
            watches.stream().forEach(x -> {
                print("Pattern : " + x.getPattern(), y -> System.out.println(y));
                prettyPrintSubstitution(x, compiledDefinition);
            });
        }
    }
}

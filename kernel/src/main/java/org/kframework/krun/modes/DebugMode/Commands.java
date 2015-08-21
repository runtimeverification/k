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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
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
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            int activeStateId = session.getActiveStateId();
            DebuggerState prevState = session.getStates().get(activeStateId);
            DebuggerState steppedState = session.step(activeStateId, stepCount);
            int effectiveStepCount = steppedState.getStepNum() - prevState.getStepNum();
            if (effectiveStepCount < stepCount) {
                System.out.println("Attempted " + stepCount + " step(s). " + "Took " + effectiveStepCount + " steps(s).");
                System.out.println("Final State Reached");
                return;
            }
            System.out.println(stepCount + " Step(s) Taken.");
            CommandUtils.displayWatches(steppedState.getWatchList(), compiledDefinition);
        }
    }

    public static class WatchCommand implements Command {
        private Optional<String> pattern;

        public WatchCommand(Optional<String> pattern) {
            this.pattern = pattern;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            pattern.ifPresent(pattern -> {
                session.addWatch(pattern);
            });
            CommandUtils.displayWatches(
                    session.getActiveState().getWatchList(),
                    compiledDefinition
            );
        }
    }
    public static class PeekCommand implements Command {

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            DebuggerState requestedState = session.getActiveState();
            if (requestedState != null) {
                prettyPrint(compiledDefinition, OutputModes.PRETTY, s -> System.out.println(s), requestedState.getCurrentK());
            } else {
                System.out.println("Requested State/Configuration Unreachable");
            }
        }
    }

    public static class BackStepCommand implements Command {

        private int backStepCount;

        public BackStepCommand(int backStepCount) {
            this.backStepCount = backStepCount;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            int activeConfigurationId = session.getActiveState().getStepNum();
            if ((backStepCount - 1) > activeConfigurationId) {
                System.out.println("Number of Configuration(s) is " + (activeConfigurationId + 1) + ". Step Count to go back must be in range [0, " + (activeConfigurationId + 1) + ")");
                return;
            }
            DebuggerState backSteppedState = session.backStep(session.getActiveStateId(), backStepCount);
            if (backSteppedState == null) {
                System.out.println("Already at Start State, Cannot take steps.");
                return;
            }
            System.out.println("Took -" + backStepCount + " step(s)");
            CommandUtils.displayWatches(backSteppedState.getWatchList(), compiledDefinition);
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
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            int requestedState = stateNum.orElse(session.getActiveStateId());
            DebuggerState nextState = session.setState(requestedState);
            if (nextState == null) {
                System.out.println("State Number specified does not exist");
                return;
            } else if (!configurationNum.isPresent()) {
                System.out.println("Selected State " + requestedState);
            } else {
                int requestedConfig = configurationNum.get();
                DebuggerState finalState = session.jumpTo(requestedState, requestedConfig);
                if (finalState == null) {
                    System.out.println("Requested Step Number couldn't be selected.");
                    return;
                } else if (!stateNum.isPresent()) {
                    System.out.println("Jumped to Step Number " + requestedConfig);
                } else {
                    System.out.println("Jumped to State Number " + requestedState + " and Step Number " + requestedConfig);
                }
                CommandUtils.displayWatches(finalState.getWatchList(), compiledDefinition);
                return;
            }
            CommandUtils.displayWatches(nextState.getWatchList(), compiledDefinition);
        }

    }

    public static class QuitCommand implements Command {

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            return;
        }
    }

    public static class ResumeCommand implements Command {
        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            DebuggerState currentState = session.getStates().get(session.getActiveStateId());
            DebuggerState finalState = session.resume();
            System.out.println(finalState.getStepNum() - currentState.getStepNum() + "Step(s) Taken");
            CommandUtils.displayWatches(finalState.getWatchList(), compiledDefinition);
        }
    }

    public static class CheckpointCommand implements Command {
        private int checkpointInterval;

        public CheckpointCommand(int checkpointInterval) {
            this.checkpointInterval = checkpointInterval;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            if (checkpointInterval <= 0) {
                System.out.println("Checkpoint Value must be >= 1");
                return;
            }
            session.setCheckpointInterval(checkpointInterval);
            System.out.println("Checkpointing Interval set to " + checkpointInterval);
            return;
        }
    }


    public static class ShowCommand implements Command {
        private String pattern;

        public ShowCommand(String pattern) {
            this.pattern = pattern;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            DebuggerMatchResult result = session.match(pattern);
            CommandUtils.prettyPrintSubstitution(result, compiledDefinition);
        }

    }

    private static class CommandUtils {

        private static void prettyPrintSubstitution(DebuggerMatchResult result, CompiledDefinition compiledDefinition) {
            List<Map<KVariable, K>> substList = result.getSubstitutions();

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
                                        prettyPrint(compiledDefinition, OutputModes.PRETTY, s -> System.out.print(s), x.getKey());
                                        System.out.print(" ---> ");
                                        prettyPrint(compiledDefinition, OutputModes.PRETTY, s -> System.out.println(s), x.getValue());
                                    }));


        }

        private static void displayWatches(List<DebuggerMatchResult> watches, CompiledDefinition compiledDefinition) {
            if (watches.isEmpty()) {
                return;
            }
            System.out.println("Watches:");
            watches.stream().forEach(x -> {
                System.out.println("Pattern : " + x.getPattern());
                prettyPrintSubstitution(x, compiledDefinition);
            });
        }
    }
}

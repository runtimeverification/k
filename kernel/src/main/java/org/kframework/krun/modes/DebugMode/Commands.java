// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes.DebugMode;

import org.kframework.backend.unparser.OutputModes;
import org.kframework.debugger.DebuggerState;
import org.kframework.debugger.KDebug;
import org.kframework.kompile.CompiledDefinition;

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
                System.out.println("Number of Configuration(s) is " + (activeConfigurationId + 1) + ". Step Count to go back must be in range [0, " + (activeConfigurationId + 1) + "]");
                return;
            }
            DebuggerState backSteppedState = session.backStep(session.getActiveStateId(), backStepCount);
            if (backSteppedState == null) {
                System.out.println("Already at Start State, Cannot take steps.");
                return;
            }
            System.out.println("Took -" + backStepCount + " step(s)");
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
                System.out.println("Requested State couldn't be selected");
            } else if (!configurationNum.isPresent()) {
                System.out.println("Selected State " + requestedState);
            } else {
                int requestedConfig = configurationNum.orElse(nextState.getStepNum());
                DebuggerState finalState = session.jumpTo(requestedState, requestedConfig);
                if (finalState == null) {
                    System.out.println("Requested configuration couldn't be selected.");
                } else {
                    System.out.println("Selected State " + requestedState + " and configuration " + requestedConfig);
                }
            }
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
        }
    }
}

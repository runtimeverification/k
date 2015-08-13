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
                System.out.println("Attempted " + stepCount + " step(s). " + "Took " + effectiveStepCount + " steps(s)");
                System.out.println("KDebug may have encountered a final configuration");
                return;
            }
            System.out.println(stepCount + " Step(s) Taken");
        }
    }

    public static class PeekCommand implements Command {

        private Optional<Integer> stateNum;

        private Optional<Integer> configurationNum;

        public PeekCommand(Optional<Integer> stateNum, Optional<Integer> configurationNum) {
            this.stateNum = stateNum;
            this.configurationNum = configurationNum;
        }

        @Override
        public void runCommand(KDebug session, CompiledDefinition compiledDefinition) {
            DebuggerState requestedState = session.peek(stateNum, configurationNum);
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
            int activeStateId = session.getActiveStateId();
            if ((backStepCount-1) > activeStateId) {
                System.out.println("Number of Configuration(s) is " + (activeStateId + 1) + " Back Step Count must be in range [0, " + activeStateId + "]");
                return;
            }
            DebuggerState backSteppedState = session.backStep(activeStateId, backStepCount);
            if (backSteppedState == null) {
                System.out.println("Couldn't retrieve previous state");
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
            DebuggerState nextState = session.setState(stateNum.orElse(session.getActiveStateId()), configurationNum);
            if (nextState == null) {
                System.out.println("Error Selecting State. State unchanged");
                return;
            }
            System.out.println("Selected State " + session.getActiveStateId());
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

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
            session.step(session.getActiveState(), stepCount);
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
            }
            else {
                System.out.println("Requested State/Configuration Unreachable");
            }
        }
    }
}

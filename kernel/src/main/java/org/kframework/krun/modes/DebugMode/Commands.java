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
 * Commands must extend {@link org.kframework.krun.modes.DebugMode.Command}.
 */
public class Commands {

    public static class StepCommand extends Command {

        private int stepCount;

        public StepCommand(KDebug session, CompiledDefinition compiledDefinition, int stepCount) {
            super(session, compiledDefinition);
            this.stepCount = stepCount;
        }

        @Override
        public void run() {
            debugSession.step(stepCount);
            System.out.println(stepCount + " Step(s) Taken");
        }
    }

    public static class PeekCommand extends Command {

        private Optional<Integer> stateNum;

        private Optional<Integer> configurationNum;

        public PeekCommand(KDebug debugSession, CompiledDefinition compiledDef, Optional<Integer> stateNum, Optional<Integer> configurationNum) {
            super(debugSession, compiledDef);
            this.stateNum = stateNum;
            this.configurationNum = configurationNum;
        }

        @Override
        public void run() {
            if (stateNum == SHOW_CURRENT_STATE_FLAG) {
                DebuggerState currentState = debugSession.getActiveState();
                if (configurationNum == SHOW_CURRENT_STATE_FLAG || configurationNum == currentState.getStepNum()) {
                    prettyPrint(compiledDef, OutputModes.PRETTY, s -> System.out.println(s), currentState.getCurrentK());
                    return;
                }

            }
        }
    }
}

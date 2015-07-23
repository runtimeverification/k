package org.kframework.krun.modes.DebugMode;

import org.kframework.debugger.KDebug;
import org.kframework.kompile.CompiledDefinition;

/**
 * Created by manasvi on 7/22/15.
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

        private int stateNum;

        private int stepNum;

        public PeekCommand(KDebug debugSession, CompiledDefinition compiledDef, int stepNum) {
            super(debugSession, compiledDef);
            this.stepNum = stepNum;
            this.stateNum = -1;
        }

        @Override
        public void run() {

        }
    }
}

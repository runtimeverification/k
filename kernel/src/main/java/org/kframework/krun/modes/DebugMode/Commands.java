package org.kframework.krun.modes.DebugMode;

import org.kframework.debugger.KDebug;
import org.kframework.kompile.CompiledDefinition;

/**
 * Created by manasvi on 7/22/15.
 */
public class Commands {

    public static class StepCommand implements Runnable {

        private int stepCount;

        private KDebug debugSession;

        private CompiledDefinition compiledDef;

        public StepCommand(int stepCount, KDebug debugSession, CompiledDefinition compiledDef) {
            this.stepCount = stepCount;
            this.debugSession = debugSession;
            this.compiledDef = compiledDef;
        }

        @Override
        public void run() {
            System.out.println("Step Called");
        }
    }
}

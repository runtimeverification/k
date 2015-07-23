package org.kframework.krun.modes.DebugMode;

import org.kframework.debugger.KDebug;
import org.kframework.kompile.CompiledDefinition;

/**
 * Created by manasvi on 7/23/15.
 */
public abstract class Command implements Runnable{

        protected KDebug debugSession;

        protected CompiledDefinition compiledDef;

        protected Command(KDebug debugSession, CompiledDefinition compiledDef) {
                this.debugSession = debugSession;
                this.compiledDef = compiledDef;
        }
}

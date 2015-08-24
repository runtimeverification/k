// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes.DebugMode;


import org.kframework.debugger.KDebug;
import org.kframework.kompile.CompiledDefinition;

/**
 * Created by manasvi on 7/23/15.
 */
public interface Command {

    public void runCommand(KDebug session, CompiledDefinition compiledDefinition, boolean disableOutput);
}

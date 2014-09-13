// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.kframework.backend.java.symbolic.JavaSymbolicKRunModule.MainExecutionContextModule;
import org.kframework.backend.java.symbolic.JavaSymbolicKRunModule.SimulationModule;
import org.kframework.krun.KRunFrontEnd;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BaseTestCase;
import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Module;
import com.google.inject.util.Modules;

public class JavaSymbolicKRunModuleTest extends BaseTestCase {

    @Test
    public void testCreateInjectionSimulation() {
        String[] argv = new String[] { "foo.c", "--simulation", "bar.c" };
        Module[] modules = KRunFrontEnd.getModules(argv);
        for (int i = 0; i < modules.length; i++) {
            //we have to override private modules one at a time to override private bindings
            if (modules[i] instanceof MainExecutionContextModule
                    || modules[i] instanceof SimulationModule) {
                modules[i] = Modules.override(modules[i]).with(new TestModule());
            }
        }
        Injector injector = Guice.createInjector(modules);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KRunFrontEnd);
    }
}

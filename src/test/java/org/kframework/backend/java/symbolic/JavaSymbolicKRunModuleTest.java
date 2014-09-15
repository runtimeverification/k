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

import java.util.List;

public class JavaSymbolicKRunModuleTest extends BaseTestCase {

    @Test
    public void testCreateInjectionSimulation() {
        String[] argv = new String[] { "foo.c", "--simulation", "bar.c" };
        List<Module> modules = KRunFrontEnd.getModules(argv);
        for (int i = 0; i < modules.size(); i++) {
            //we have to override private modules one at a time to override private bindings
            if (modules.get(i) instanceof MainExecutionContextModule
                    || modules.get(i) instanceof SimulationModule) {
                modules.set(i, Modules.override(modules.get(i)).with(new TestModule()));
            }
        }
        Injector injector = Guice.createInjector(modules);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KRunFrontEnd);
    }
}

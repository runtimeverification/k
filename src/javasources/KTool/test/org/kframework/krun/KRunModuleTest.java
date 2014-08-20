// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import static org.junit.Assert.*;

import java.util.HashMap;

import org.junit.Before;
import org.junit.Test;
import org.kframework.krun.KRunModule.MainExecutionContextModule;
import org.kframework.krun.KRunModule.SimulationModule;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BaseTestCase;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Module;
import com.google.inject.util.Modules;

public class KRunModuleTest extends BaseTestCase {

    @Before
    public void setUp() {
        context.configVarSorts = new HashMap<>();
    }

    @Test
    public void testCreateInjection() {
        String[] argv = new String[] { "foo.c" };
        Module[] modules = KRunFrontEnd.getModules(argv);
        Injector injector = Guice.createInjector(Modules.override(modules).with(new TestModule()));
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KRunFrontEnd);
    }

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

    public void testInvalidArguments() {
        String[] argv = new String[] { "--backend", "foobarbaz" };
        Module[] modules = KRunFrontEnd.getModules(argv);
        assertNull(modules);
    }
}

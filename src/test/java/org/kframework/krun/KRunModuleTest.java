// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import static org.junit.Assert.*;

import java.util.HashMap;
import java.util.List;

import org.junit.Before;
import org.junit.Test;
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
        List<Module> modules = KRunFrontEnd.getModules(argv);
        Injector injector = Guice.createInjector(Modules.override(modules).with(new TestModule()));
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KRunFrontEnd);
    }

    public void testInvalidArguments() {
        String[] argv = new String[] { "--backend", "foobarbaz" };
        List<Module> modules = KRunFrontEnd.getModules(argv);
        assertNull(modules);
    }
}

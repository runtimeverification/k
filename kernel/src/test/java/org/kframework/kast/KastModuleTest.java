// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kast;

import static org.junit.Assert.*;

import org.junit.Test;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BaseTestCase;
import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Module;
import com.google.inject.util.Modules;

import java.util.List;

public class KastModuleTest extends BaseTestCase {

    @Test
    public void testCreateInjection() {
        String[] argv = new String[] { "foo.c" };
        List<Module> modules = KastFrontEnd.getModules();
        Injector injector = Guice.createInjector(Modules.override(modules).with(new TestModule(), new DefinitionSpecificTestModule()));
        prepInjector(injector, "-kast", argv);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KastFrontEnd);
    }
}

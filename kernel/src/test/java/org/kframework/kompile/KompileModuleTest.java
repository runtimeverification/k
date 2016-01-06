// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.util.Modules;
import org.junit.Test;
import org.kframework.kdep.KDepFrontEnd;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BaseTestCase;

import static org.junit.Assert.*;

public class KompileModuleTest extends BaseTestCase {

    @Test
    public void testCreateInjection() {
        String[] argv = new String[] { "test.k", "--backend", "test" };
        Injector injector = Guice.createInjector(Modules.override(KompileFrontEnd.getModules()).with(new DefinitionSpecificTestModule(), new TestModule()));
        prepInjector(injector, "-kompile", argv);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KompileFrontEnd);
    }

    @Test
    public void testKDep() {
        String[] argv = new String[] { "test.k" };
        Injector injector = Guice.createInjector(Modules.override(KDepFrontEnd.getModules()).with(new DefinitionSpecificTestModule(), new TestModule()));
        prepInjector(injector, "-kdep", argv);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KDepFrontEnd);
    }
}

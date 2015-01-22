// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kdoc;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BaseTestCase;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.util.Modules;

public class KDocModuleTest extends BaseTestCase {
    @Test
    public void testCreateInjection() {
        String[] argv = new String[] { "--format", "latex" };
        Injector injector = Guice.createInjector(Modules.override(KDocFrontEnd.getModules(argv)).with(new DefinitionSpecificTestModule(), new TestModule()));
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KDocFrontEnd);
    }
}

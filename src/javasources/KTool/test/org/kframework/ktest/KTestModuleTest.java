// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.kframework.ktest.KTestFrontEnd;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BaseTestCase;
import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Module;


public class KTestModuleTest extends BaseTestCase {

    @Test
    public void testCreateInjection() {
        String[] argv = new String[] { "foo.c" };
        Module[] modules = KTestFrontEnd.getModules(argv);
        Injector injector = Guice.createInjector(modules);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KTestFrontEnd);
    }

}

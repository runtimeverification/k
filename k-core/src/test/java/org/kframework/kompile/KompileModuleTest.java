// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import static org.junit.Assert.*;

import org.junit.Test;
import org.kframework.main.FrontEnd;

import com.google.inject.Guice;
import com.google.inject.Injector;

public class KompileModuleTest {

    @Test
    public void testCreateInjection() {
        String[] argv = new String[] { "test.k" };
        Injector injector = Guice.createInjector(KompileFrontEnd.getModules(argv));
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KompileFrontEnd);
    }
}

// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

import java.io.IOException;

import org.junit.Test;
import org.kframework.backend.Backend;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.mockito.Mock;

public class KompileFrontEndTest extends BaseTestCase {

    @Mock
    Backend backend;

    @Mock
    BinaryLoader loader;

    @Mock
    DefinitionLoader defLoader;

    @Mock
    protected Stopwatch sw;

    KompileOptions options = new KompileOptions();

    @Test
    public void testHelp() throws IOException {
        when(backend.getCompilationSteps()).thenThrow(new AssertionError());
        options.global.help = true;
        new KompileFrontEnd(context, options, "foo", "", backend, sw, kem, loader, defLoader).main();
        assertEquals("foo", stdout.toString());
    }


    @Test
    public void testExperimentalHelp() throws IOException {
        when(backend.getCompilationSteps()).thenThrow(new AssertionError());
        options.global.helpExperimental = true;
        new KompileFrontEnd(context, options, "", "foo", backend, sw, kem, loader, defLoader).main();
        assertEquals("foo", stdout.toString());
    }
}

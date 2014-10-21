// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

import java.io.IOException;

import org.junit.Test;
import org.kframework.backend.Backend;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.IOTestCase;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.mockito.Mock;

public class KompileFrontEndTest extends IOTestCase {

    @Mock
    Backend backend;

    @Mock
    DefinitionLoader defLoader;

    @Mock
    JarInfo jarInfo;

    @Mock
    FileUtil files;

    KompileOptions options = new KompileOptions();

    @Test
    public void testHelp() throws IOException {
        when(backend.getCompilationSteps()).thenThrow(new AssertionError());
        options.global.help = true;
        new KompileFrontEnd(context, options, "foo", "", backend, sw, kem, loader, defLoader, jarInfo, files).main();
        assertEquals("foo", stdout.toString());
    }


    @Test
    public void testExperimentalHelp() throws IOException {
        when(backend.getCompilationSteps()).thenThrow(new AssertionError());
        options.global.helpExperimental = true;
        new KompileFrontEnd(context, options, "", "foo", backend, sw, kem, loader, defLoader, jarInfo, files).main();
        assertEquals("foo", stdout.toString());
    }

    @Test
    public void testVersion() {
        options.global.version = true;
        new KompileFrontEnd(context, options, "", "foo", backend, sw, kem, loader, defLoader, jarInfo, files).main();
        verify(jarInfo).printVersionMessage();
    }
}

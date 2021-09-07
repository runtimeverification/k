// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.util.Providers;
import org.junit.Test;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.IOTestCase;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.mockito.Mock;

import java.io.IOException;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

public class KompileFrontEndTest extends IOTestCase {

    @Mock
    org.kframework.compile.Backend koreBackend;

    @Mock
    JarInfo jarInfo;

    @Mock
    FileUtil files;

    KompileOptions options = new KompileOptions();
    GlobalOptions globalOptions = new GlobalOptions();

    @Test
    public void testHelp() throws IOException {
        globalOptions.help = true;
        new KompileFrontEnd(options, globalOptions,"foo", Providers.of(koreBackend), sw, kem, loader, jarInfo, Providers.of(files)).main();
        assertEquals("foo", stdout.toString());
    }

    @Test
    public void testVersion() {
        globalOptions.version = true;
        new KompileFrontEnd(options, globalOptions, "", Providers.of(koreBackend), sw, kem, loader, jarInfo, Providers.of(files)).main();
        verify(jarInfo).printVersionMessage();
    }
}

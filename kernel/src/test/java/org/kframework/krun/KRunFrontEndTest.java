// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.krun;

import com.google.inject.util.Providers;
import org.junit.Ignore;
import org.junit.Test;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.file.JarInfo;
import org.mockito.Mock;

import static org.mockito.Mockito.*;

public class KRunFrontEndTest extends BaseTestCase {

    @Mock
    JarInfo jarInfo;

    @Test
    public void testVersion() {
        GlobalOptions options = new GlobalOptions();
        options.version = true;
        KRunFrontEnd frontend = new KRunFrontEnd(options, null, null, jarInfo, scope, Providers.of(kompiledDir), kem, new KRunOptions(), Providers.of(files), null, null, null, null);
        frontend.main();
        verify(jarInfo).printVersionMessage();
    }

    @Test @Ignore
    public void testNothingAvailable() {
        GlobalOptions options = new GlobalOptions();
        KRunFrontEnd frontend = new KRunFrontEnd(options, null, null, jarInfo, scope, Providers.of(kompiledDir), kem, new KRunOptions(), Providers.of(files), null, null, null, null);
        frontend.main();
        verify(kem).print();
    }
}

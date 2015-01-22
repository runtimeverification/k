// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import static org.mockito.Mockito.*;

import org.junit.Test;
import org.kframework.main.GlobalOptions;
import org.kframework.transformation.Transformation;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.errorsystem.KEMExceptionProvider;
import org.kframework.utils.file.JarInfo;
import org.mockito.Mock;

public class KRunFrontEndTest extends BaseTestCase {

    @Mock
    JarInfo jarInfo;

    @Test
    public void testVersion() {
        GlobalOptions options = new GlobalOptions();
        options.version = true;
        KRunFrontEnd frontend = new KRunFrontEnd(options, null, null, new KEMExceptionProvider<Transformation<Void, Void>>(), kem, loader, jarInfo, files);
        frontend.main();
        verify(jarInfo).printVersionMessage();
    }

    @Test
    public void testNothingAvailable() {
        GlobalOptions options = new GlobalOptions();
        KRunFrontEnd frontend = new KRunFrontEnd(options, null, null, new KEMExceptionProvider<Transformation<Void, Void>>(), kem, loader, jarInfo, files);
        frontend.main();
        verify(kem).print();
    }
}

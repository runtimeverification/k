// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import static org.mockito.Mockito.*;

import org.junit.Test;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.KRun;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.errorsystem.KEMExceptionProvider;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;
import org.mockito.Matchers;
import org.kframework.utils.file.JarInfo;
import org.mockito.Mock;

import com.google.common.base.Optional;

public class KRunFrontEndTest extends BaseTestCase {

    @Mock
    JarInfo jarInfo;

    @Test
    public void testVersion() {
        KRunOptions options = new KRunOptions();
        options.global.version = true;
        KRunFrontEnd frontend = new KRunFrontEnd(options, "", "",
                new KEMExceptionProvider<KRun>(), new KEMExceptionProvider<Context>(),
                new KEMExceptionProvider<Term>(), sw, kem, loader, jarInfo);
        frontend.main();
        verify(jarInfo).printVersionMessage();
    }

    @Test
    public void testNothingAvailable() {
        KRunOptions options = new KRunOptions();
        KRunFrontEnd frontend = new KRunFrontEnd(options, "", "",
                new KEMExceptionProvider<KRun>(), new KEMExceptionProvider<Context>(),
                new KEMExceptionProvider<Term>(), sw, kem, loader, jarInfo);
        frontend.main();
        verify(kem).print();
    }
}

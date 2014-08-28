// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils;

import static org.mockito.Mockito.*;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import org.junit.After;
import org.junit.Before;
import org.junit.runner.RunWith;
import org.kframework.kil.Configuration;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import com.google.inject.AbstractModule;

@RunWith(MockitoJUnitRunner.class)
public abstract class BaseTestCase {

    @Mock
    protected Context context;

    @Mock
    protected Configuration configuration;

    @Mock
    protected KExceptionManager kem;

    @Mock
    protected Stopwatch sw;

    @Mock
    protected BinaryLoader loader;

    PrintStream oldOut, oldErr;
    protected ByteArrayOutputStream stdout = new ByteArrayOutputStream();
    protected ByteArrayOutputStream stderr = new ByteArrayOutputStream();

    @Before
    public void setUpWiring() {
        context.kompileOptions = new KompileOptions();
    }

    @Before
    public void setUpIO() {
        oldOut = System.out;
        oldErr = System.err;
        System.setOut(new PrintStream(stdout));
        System.setErr(new PrintStream(stderr));
    }

    @After
    public void tearDownIO() {
        System.setOut(oldOut);
        System.setErr(oldErr);
    }

    public class TestModule extends AbstractModule {

        @Override
        protected void configure() {
            bind(Context.class).toInstance(context);
            bind(Configuration.class).toInstance(configuration);
        }

    }
}

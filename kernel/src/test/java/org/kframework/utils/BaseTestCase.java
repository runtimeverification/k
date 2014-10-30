// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.File;
import java.util.Map;

import org.junit.Before;
import org.junit.runner.RunWith;
import org.kframework.kil.Configuration;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.RunProcess;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.WorkingDir;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import com.google.inject.AbstractModule;
import com.google.inject.TypeLiteral;

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

    @Mock
    protected RunProcess rp;

    @Mock
    File kompiledDir;

    @Mock
    File definitionDir;

    @Mock
    File tempDir;

    @Before
    public void setUpWiring() {
        context.kompileOptions = new KompileOptions();
    }

    public class DefinitionSpecificTestModule extends AbstractModule {

        @Override
        protected void configure() {
            bind(Context.class).toInstance(context);
            bind(Configuration.class).toInstance(configuration);
        }

    }

    public class TestModule extends AbstractModule {

        @Override
        protected void configure() {
            bind(RunProcess.class).toInstance(rp);
            bind(File.class).annotatedWith(WorkingDir.class).toInstance(new File("."));
            bind(new TypeLiteral<Map<String, String>>() {}).annotatedWith(Environment.class).toInstance(System.getenv());
        }

    }
}

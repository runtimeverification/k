// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.File;

import com.google.inject.multibindings.MapBinder;
import org.junit.Before;
import org.junit.runner.RunWith;
import org.kframework.kdoc.KDocOptions;
import org.kframework.backend.Backend;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.RunProcess;
import org.kframework.main.Main;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.SimpleScope;
import org.kframework.utils.inject.Concrete;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import com.google.inject.AbstractModule;
import com.google.inject.Injector;
import com.google.inject.Key;
import com.google.inject.Provides;
import com.google.inject.name.Names;

@RunWith(MockitoJUnitRunner.class)
public abstract class BaseTestCase {

    @Mock
    protected Context context;

    @Mock
    protected Definition definition;

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
    protected
    File kompiledDir;

    @Mock
    File definitionDir;

    @Mock
    File tempDir;

    @Mock
    protected FileUtil files;

    @Mock
    protected DefinitionScope scope;

    @Before
    public void setUpWiring() {
        context.kompileOptions = new KompileOptions();
    }

    public class DefinitionSpecificTestModule extends AbstractModule {

        @Override
        protected void configure() {
            bind(KompileOptions.class).toInstance(context.kompileOptions);
            bind(Definition.class).toInstance(definition);
            bind(Configuration.class).toInstance(configuration);
            bind(File.class).annotatedWith(KompiledDir.class).toInstance(kompiledDir);
            bind(Definition.class).annotatedWith(Concrete.class).toInstance(definition);
        }

        @Provides
        Context context() {
            return context;
        }
    }

    public class TestModule extends AbstractModule {

        @Override
        protected void configure() {
            bind(RunProcess.class).toInstance(rp);
            bind(KDocOptions.class).toInstance(new KDocOptions());
            bind(KRunOptions.class).toInstance(new KRunOptions());
            MapBinder<String, Backend> mapBinder = MapBinder.newMapBinder(binder(), String.class, Backend.class);
            mapBinder.addBinding("test").to(TestBackend.class);
        }

    }

    public void prepInjector(Injector injector, String tool, String[] args) {
        SimpleScope scope = injector.getInstance(Key.get(SimpleScope.class, Names.named("requestScope")));
        scope.enter();
        Main.seedInjector(scope, tool, args, new File("."), System.getenv());
    }
}

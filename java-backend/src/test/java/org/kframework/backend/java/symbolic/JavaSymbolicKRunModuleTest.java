// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.beust.jcommander.internal.Lists;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.inject.AbstractModule;
import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Key;
import com.google.inject.Module;
import com.google.inject.util.Modules;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.kframework.backend.java.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kompile.KompileFrontEnd;
import org.kframework.krun.KRunFrontEnd;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.inject.Main;
import org.mockito.Mock;

import java.util.HashMap;
import java.util.List;

import static org.junit.Assert.*;

public class JavaSymbolicKRunModuleTest extends BaseTestCase {

    @Mock
    Definition definition;

    @Before
    public void setUp() {
        context.klabels = HashMultimap.<String, Production>create();
        context.configVarSorts = new HashMap<>();
    }

    @Test
    public void testCreateInjectionJava() {
        context.kompileOptions.backend = "java";
        String[] argv = new String[] { "foo.c" };
        List<Module> definitionSpecificModules = Lists.newArrayList(KRunFrontEnd.getDefinitionSpecificModules());
        definitionSpecificModules.addAll(new JavaBackendKModule().getDefinitionSpecificKRunModules());
        Module definitionSpecificModuleOverride = Modules.override(definitionSpecificModules).with(new TestModule());
        List<Module> modules = Lists.newArrayList(KRunFrontEnd.getModules(ImmutableList.of(definitionSpecificModuleOverride)));
        modules.addAll(new JavaBackendKModule().getKRunModules(ImmutableList.of(definitionSpecificModuleOverride)));
        Injector injector = Guice.createInjector(Modules.override(modules).with(new BaseTestCase.TestModule()));
        prepInjector(injector, "-krun", argv);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KRunFrontEnd);
        injector.getInstance(Key.get(ExecutionMode.class, Main.class));
        injector.getInstance(Key.get(InitializeRewriter.class, Main.class));
    }

    @Test
    public void testCreateInjectionJavaKompile() {
        String[] argv = new String[] { "foo.k", "--backend", "java" };
        List<Module> modules = Lists.newArrayList(KompileFrontEnd.getModules());
        modules.addAll(new JavaBackendKModule().getKompileModules());
        Injector injector = Guice.createInjector(Modules.override(modules).with(new TestModule(), new BaseTestCase.TestModule()));
        prepInjector(injector, "-kompile", argv);
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KompileFrontEnd);
    }

    public class TestModule extends AbstractModule {
        @Override
        protected void configure() {
            install(new DefinitionSpecificTestModule());
            bind(Definition.class).toInstance(definition);
        }
    }
}

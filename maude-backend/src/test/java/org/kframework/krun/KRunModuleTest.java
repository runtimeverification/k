// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import static org.junit.Assert.*;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;
import org.kframework.backend.maude.MaudeBackendKModule;
import org.kframework.kil.KSequence;
import org.kframework.kil.Term;
import org.kframework.krun.api.SearchResult;
import org.kframework.krun.tools.Debugger;
import org.kframework.krun.tools.Executor;
import org.kframework.krun.tools.LtlModelChecker;
import org.kframework.main.FrontEnd;
import org.kframework.transformation.Transformation;
import org.kframework.transformation.TransformationProvider;
import org.kframework.utils.BaseTestCase;

import static org.mockito.Mockito.*;

import com.beust.jcommander.internal.Lists;
import com.google.common.collect.ImmutableList;
import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Key;
import com.google.inject.Module;
import com.google.inject.ProvisionException;
import com.google.inject.TypeLiteral;
import com.google.inject.spi.Message;
import com.google.inject.util.Modules;

public class KRunModuleTest extends BaseTestCase {

    @Before
    public void setUp() {
        context.configVarSorts = new HashMap<>();
        when(rp.runParser("kast", "foo.c", false, null, context)).thenReturn(KSequence.EMPTY);
    }

    @Test
    public void testCreateInjectionMaude() {
        String[] argv = new String[] { "foo.c" };
        Injector injector = buildInjector(argv);
        injector.getInstance(Executor.Tool.class);
    }

    @Test
    public void testCreateInjectionLtl() {
        String[] argv = new String[] { "foo.c", "--ltlmc", "TrueLtl" };
        Injector injector = buildInjector(argv);
        injector.getInstance(LtlModelChecker.Tool.class);
    }

    @Test
    public void testCreateInjectionDebuggerPretty() {
        String[] argv = new String[] { "foo.c", "--debugger" };
        Injector injector = buildInjector(argv);
        injector.getInstance(Debugger.Tool.class);
    }

    @Test
    public void testCreateInjectionDebuggerKast() {
        String[] argv = new String[] { "foo.c", "--debugger", "--output", "kast" };
        Injector injector = buildInjector(argv);
        injector.getInstance(Key.get(new TypeLiteral<TransformationProvider<Transformation<SearchResult, Map<String, Term>>>>() {}));
        injector.getInstance(Debugger.Tool.class);
    }

    @Test
    public void testCreateInjectionDebuggerRaw() {
        String[] argv = new String[] { "foo.c", "--debugger", "--output", "raw" };
        Injector injector = buildInjector(argv);
        try {
            injector.getInstance(Debugger.Tool.class);
        } catch (ProvisionException e) {
            for (Message msg : e.getErrorMessages()) {
                msg.getCause().printStackTrace();
            }
            throw e;
        }
    }

    private Injector buildInjector(String[] argv) {
        List<Module> definitionSpecificModules = Lists.newArrayList(KRunFrontEnd.getDefinitionSpecificModules(argv));
        definitionSpecificModules.addAll(new MaudeBackendKModule().getDefinitionSpecificKRunModules());
        Module definitionSpecificModuleOverride = Modules.override(definitionSpecificModules).with(new DefinitionSpecificTestModule());
        List<Module> modules = Lists.newArrayList(KRunFrontEnd.getModules(argv, ImmutableList.of(definitionSpecificModuleOverride)));
        modules.addAll(new MaudeBackendKModule().getKRunModules(ImmutableList.of(definitionSpecificModuleOverride)));
        Injector injector = Guice.createInjector(Modules.override(modules).with(new TestModule()));
        assertTrue(injector.getInstance(FrontEnd.class) instanceof KRunFrontEnd);
        injector.getInstance(Key.get(new TypeLiteral<TransformationProvider<Transformation<Void, Void>>>() {}));
        return injector;
    }

    public void testInvalidArguments() {
        String[] argv = new String[] { "--backend", "foobarbaz" };
        List<Module> modules = KRunFrontEnd.getModules(argv, KRunFrontEnd.getDefinitionSpecificModules(argv));
        assertNull(modules);
    }
}

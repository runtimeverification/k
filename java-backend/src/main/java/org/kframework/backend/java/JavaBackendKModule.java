// Copyright (c) 2015-2019 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.java;

import com.google.inject.AbstractModule;
import com.google.inject.Binder;
import com.google.inject.Module;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import com.google.inject.name.Names;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.InitializeRewriter;
import org.kframework.backend.java.symbolic.JavaBackend;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.compile.Backend;
import org.kframework.definition.Definition;
import org.kframework.main.AbstractKModule;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.inject.Options;

import java.util.Collections;
import java.util.List;
import java.util.function.Function;

/**
 * Created by dwightguth on 5/27/15.
 */
public class JavaBackendKModule extends AbstractKModule {

    @Override
    public List<Pair<Class<?>, Boolean>> krunOptions() {
        return Collections.singletonList(Pair.of(JavaExecutionOptions.class, true));
    }

    @Override
    public List<Pair<Class<?>, Boolean>> kproveOptions() {
        return Collections.singletonList(Pair.of(JavaExecutionOptions.class, true));
    }

    @Override
    public List<Module> getKompileModules() {
        List<Module> mods = super.getKompileModules();
        mods.add(new AbstractModule() {
            @Override
            protected void configure() {
                installJavaBackend(binder());
            }
            });
        return mods;
    }

    private void installJavaBackend(Binder binder) {
        MapBinder<String, Backend> mapBinder = MapBinder.newMapBinder(
                binder, String.class, Backend.class);
        mapBinder.addBinding("java").to(JavaBackend.class);
    }

    @Override
    public List<Module> getKRunModules() {
        List<Module> mods = super.getKRunModules();
        mods.add(new AbstractModule() {
            @Override
            protected void configure() {
                bindOptions(JavaBackendKModule.this::krunOptions, binder());

                installJavaRewriter(binder());

                MapBinder<String, Integer> checkPointBinder = MapBinder.newMapBinder(
                        binder(), String.class, Integer.class, Names.named("checkpointIntervalMap"));
                checkPointBinder.addBinding("java").toInstance(50); //TODO(dwightguth): finesse this number

                Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
                experimentalOptionsBinder.addBinding().toInstance(JavaExecutionOptions.class);
            }
        });
        return mods;
    }

    @Override
    public List<Module> getKProveModules() {
        List<Module> mods = super.getKProveModules();
        mods.add(new AbstractModule() {
            @Override
            protected void configure() {
                bindOptions(JavaBackendKModule.this::kproveOptions, binder());

                installJavaBackend(binder());
                installJavaRewriter(binder());

                Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
                experimentalOptionsBinder.addBinding().toInstance(JavaExecutionOptions.class);
            }
        });
        return mods;
    }

    private void installJavaRewriter(Binder binder) {
        MapBinder<String, Function<Definition, Rewriter>> rewriterBinder = MapBinder.newMapBinder(
                binder, TypeLiteral.get(String.class), new TypeLiteral<Function<Definition, Rewriter>>() {
                });
        rewriterBinder.addBinding("java").to(InitializeRewriter.class);
    }

    @Override
    public List<Module> getDefinitionSpecificKEqModules() {
        List<Module> mods = super.getDefinitionSpecificKEqModules();
        mods.add(new AbstractModule() {
            @Override
            protected void configure() {
                installJavaBackend(binder());
                installJavaRewriter(binder());
            }
        });
        return mods;
    }
}

// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.main;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.Backend;
import org.kframework.backend.PosterBackend;
import org.kframework.krun.tools.Executor;
import org.kframework.krun.tools.LtlModelChecker;
import org.kframework.krun.tools.Prover;
import org.kframework.main.KModule;
import org.kframework.utils.inject.Builtins;
import org.kframework.utils.inject.Options;

import com.google.common.collect.Lists;
import com.google.inject.AbstractModule;
import com.google.inject.Binder;
import com.google.inject.Module;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;

public abstract class AbstractKModule implements KModule {

    public List<Pair<String, Class<? extends Backend>>> backends() {
        return Collections.emptyList();
    }

    public List<Pair<String, Class<? extends PosterBackend>>> posterTypes() {
        return Collections.emptyList();
    }

    public List<Pair<Object, Boolean>> kompileOptions() {
        return Collections.emptyList();
    }

    public List<Pair<Object, Boolean>> krunOptions() {
        return Collections.emptyList();
    }

    public List<Pair<String, Class<? extends Executor>>> executors() {
        return Collections.emptyList();
    }

    public List<Pair<String, Class<? extends LtlModelChecker>>> ltlModelCheckers() {
        return Collections.emptyList();
    }

    public List<Pair<String, Class<? extends Prover>>> provers() {
        return Collections.emptyList();
    }

    public Map<String, String> javaBackendHooks() {
        return Collections.emptyMap();
    }

    @Override
    public List<Module> getKDocModules() {
        return Collections.<Module>singletonList(new AbstractModule() {

            @Override
            protected void configure() {
                MapBinder<String, PosterBackend> mapBinder = MapBinder.newMapBinder(
                        binder(), String.class, PosterBackend.class);
                for (Pair<String, Class<? extends PosterBackend>> backend : posterTypes()) {
                    mapBinder.addBinding(backend.getKey()).to(backend.getValue());
                }
            }
        });
    }

    private void bindOptions(Supplier<List<Pair<Object, Boolean>>> action, Binder binder) {
        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder, Object.class, Options.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder, new TypeLiteral<Class<?>>() {}, Options.class);
        for (Pair<Object, Boolean> option : action.get()) {
            optionsBinder.addBinding().toInstance(option.getKey());
            // we are actually deliberately breaking the type theory of Java here because there's no other
            // way to make this method call type correctly. Clearly it would be very bad to do this if we didn't know
            // in advance that the class pointed to an instance of the exact same class as the object, but
            // we got it from the object itself, so this should be safe, even though it's technically an incorrect cast.
            @SuppressWarnings("unchecked")
            Class<Object> unsafelyCastClass = (Class<Object>) option.getKey().getClass();
            binder.bind(unsafelyCastClass).toInstance(option.getKey());
            if (option.getValue()) {
                experimentalOptionsBinder.addBinding().toInstance(option.getKey().getClass());
            }
        }
    }

    private void bindJavaBackendHooks(Binder binder) {
        MapBinder<String, String> builtinMethods = MapBinder.newMapBinder(binder,
                String.class, String.class, Builtins.class);
        for (Map.Entry<String, String> entry : javaBackendHooks().entrySet()) {
            builtinMethods.addBinding(entry.getKey()).toInstance(entry.getValue());
        }
    }

    @Override
    public List<Module> getKompileModules() {
        return Lists.newArrayList(new AbstractModule() {

            @Override
            protected void configure() {
                bindOptions(AbstractKModule.this::kompileOptions, binder());

                MapBinder<String, Backend> mapBinder = MapBinder.newMapBinder(
                        binder(), String.class, Backend.class);
                for (Pair<String, Class<? extends Backend>> backend : backends()) {
                    mapBinder.addBinding(backend.getKey()).to(backend.getValue());
                }

                bindJavaBackendHooks(binder());
            }
        });
    }

    @Override
    public List<Module> getKastModules() {
        return Lists.newArrayList();
    }

    @Override
    public List<Module> getKRunModules(List<Module> definitionSpecificModules) {
        return Lists.newArrayList(new AbstractModule() {

            @Override
            protected void configure() {
                bindOptions(AbstractKModule.this::krunOptions, binder());
            }
        });
    }

    @Override
    public List<Module> getDefinitionSpecificKRunModules() {
        return Lists.newArrayList(new AbstractModule() {

            @Override
            protected void configure() {
                //bind backend implementations of tools to their interfaces
                MapBinder<String, Executor> executorBinder = MapBinder.newMapBinder(
                        binder(), String.class, Executor.class);
                for (Pair<String, Class<? extends Executor>> executor : executors()) {
                    executorBinder.addBinding(executor.getKey()).to(executor.getValue());
                }

                MapBinder<String, LtlModelChecker> ltlBinder = MapBinder.newMapBinder(
                        binder(), String.class, LtlModelChecker.class);
                for (Pair<String, Class<? extends LtlModelChecker>> modelChecker : ltlModelCheckers()) {
                    ltlBinder.addBinding(modelChecker.getKey()).to(modelChecker.getValue());
                }

                MapBinder<String, Prover> proverBinder = MapBinder.newMapBinder(
                        binder(), String.class, Prover.class);
                for (Pair<String, Class<? extends Prover>> prover : provers()) {
                    proverBinder.addBinding(prover.getKey()).to(prover.getValue());
                }
                bindJavaBackendHooks(binder());
            }
        });
    }

    @Override
    public List<Module> getKTestModules() {
        return Lists.newArrayList();
    }

}

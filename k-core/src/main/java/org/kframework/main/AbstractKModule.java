// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.main;

import java.util.Collections;
import java.util.List;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.Backend;
import org.kframework.krun.tools.Executor;
import org.kframework.krun.tools.LtlModelChecker;
import org.kframework.krun.tools.Prover;
import org.kframework.main.KModule;
import org.kframework.utils.inject.Options;

import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;

public abstract class AbstractKModule implements KModule {

    public List<Pair<String, Class<? extends Backend>>> backends() {
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

    @Override
    public List<Module> getKompileModules() {
        return Collections.<Module>singletonList(new AbstractModule() {

            @Override
            protected void configure() {
                Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
                Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
                for (Pair<Object, Boolean> option : kompileOptions()) {
                    optionsBinder.addBinding().toInstance(option.getKey());
                    if (option.getValue()) {
                        experimentalOptionsBinder.addBinding().toInstance(option.getKey().getClass());
                    }
                }

                MapBinder<String, Backend> mapBinder = MapBinder.newMapBinder(
                        binder(), String.class, Backend.class);
                for (Pair<String, Class<? extends Backend>> backend : backends()) {
                    mapBinder.addBinding(backend.getKey()).to(backend.getValue());
                }
            }
        });
    }

    @Override
    public List<Module> getKastModules() {
        return Collections.emptyList();
    }

    @Override
    public List<Module> getKRunModules(List<Module> definitionSpecificModules) {
        return Collections.<Module>singletonList(new AbstractModule() {

            @Override
            protected void configure() {
                Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
                Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
                for (Pair<Object, Boolean> option : krunOptions()) {
                    optionsBinder.addBinding().toInstance(option.getKey());
                    if (option.getValue()) {
                        experimentalOptionsBinder.addBinding().toInstance(option.getKey().getClass());
                    }
                }
            }
        });
    }

    @Override
    public List<Module> getDefinitionSpecificKRunModules() {
        return Collections.<Module>singletonList(new AbstractModule() {

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
            }
        });
    }

    @Override
    public List<Module> getKTestModules() {
        return Collections.emptyList();
    }

}

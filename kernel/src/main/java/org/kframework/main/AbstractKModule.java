// Copyright (c) K Team. All Rights Reserved.
package org.kframework.main;

import com.google.common.collect.Lists;
import com.google.inject.AbstractModule;
import com.google.inject.Binder;
import com.google.inject.Module;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.PosterBackend;
import org.kframework.utils.inject.Builtins;
import org.kframework.utils.inject.Options;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

public abstract class AbstractKModule implements KModule {

    public List<Pair<String, Class<? extends PosterBackend>>> posterTypes() {
        return Collections.emptyList();
    }

    public List<Pair<Class<?>, Boolean>> kompileOptions() {
        return Collections.emptyList();
    }

    public List<Pair<Class<?>, Boolean>> krunOptions() {
        return Collections.emptyList();
    }

    public List<Pair<Class<?>, Boolean>> kproveOptions() {
        return Collections.emptyList();
    }

    public Map<String, String> javaBackendHooks() {
        return Collections.emptyMap();
    }

    protected void bindOptions(Supplier<List<Pair<Class<?>, Boolean>>> action, Binder binder) {
        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder, Object.class, Options.class);
        for (Pair<Class<?>, Boolean> option : action.get()) {
            optionsBinder.addBinding().to(option.getKey());
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

                bindJavaBackendHooks(binder());
            }
        });
    }

    @Override
    public List<Module> getKastModules() {
        return Lists.newArrayList();
    }

    @Override
    public List<Module> getKRunModules() {
        return Lists.newArrayList(new AbstractModule() {

            @Override
            protected void configure() {
                bindOptions(AbstractKModule.this::krunOptions, binder());
                bindJavaBackendHooks(binder());
            }
        });
    }

    @Override
    public List<Module> getKEqModules(List<Module> definitionSpecificModules) {
        return Lists.newArrayList();
    }

    @Override
    public List<Module> getDefinitionSpecificKEqModules() {
        return Lists.newArrayList(new AbstractModule() {

            @Override
            protected void configure() {
                //bind backend implementations of tools to their interfaces
                bindJavaBackendHooks(binder());
            }
        });
    }

    @Override
    public List<Module> getKProveModules() {
        return Lists.newArrayList(new AbstractModule() {

            @Override
            protected void configure() {
                bindOptions(AbstractKModule.this::kproveOptions, binder());
                bindJavaBackendHooks(binder());
            }
        });
    }
}

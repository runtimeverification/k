// Copyright (c) 2015-2019 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.llvm;

import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.definition.Definition;
import org.kframework.main.AbstractKModule;
import org.kframework.rewriter.Rewriter;

import java.util.Collections;
import java.util.List;
import java.util.function.Function;

/**
 * Created by traiansf on 9/13/18.
 */
public class LLVMBackendKModule extends AbstractKModule {

    @Override
    public List<Module> getKompileModules() {
        List<Module> mods = super.getKompileModules();
        mods.add(new AbstractModule() {
            @Override
            protected void configure() {
                bindOptions(LLVMBackendKModule.this::kompileOptions, binder());

                MapBinder<String, org.kframework.compile.Backend> mapBinder = MapBinder.newMapBinder(
                        binder(), String.class, org.kframework.compile.Backend.class);
                mapBinder.addBinding("llvm").to(LLVMBackend.class);
            }
        });
        return mods;
    }

    @Override
    public List<Pair<Class<?>, Boolean>> kompileOptions() {
        return Collections.singletonList(Pair.of(LLVMKompileOptions.class, true));
    }

    @Override
    public List<Module> getKRunModules() {
        return Collections.singletonList(new AbstractModule() {
            @Override
            protected void configure() {
                MapBinder<String, Function<Definition, Rewriter>> rewriterBinder = MapBinder.newMapBinder(
                        binder(), TypeLiteral.get(String.class), new TypeLiteral<Function<Definition, Rewriter>>() {
                        });
                rewriterBinder.addBinding("llvm").to(LLVMRewriter.class);

            }
        });
    }
}

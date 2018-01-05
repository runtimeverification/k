// Copyright (c) 2015-2016 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.java;

import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.name.Names;
import org.kframework.backend.java.symbolic.InitializeRewriter;
import org.kframework.backend.java.symbolic.JavaBackend;
import org.kframework.backend.java.symbolic.ProofExecutionMode;
import org.kframework.krun.ToolActivation;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.AbstractKModule;
import org.kframework.rewriter.Rewriter;

import java.util.Collections;
import java.util.List;
import java.util.function.Function;

/**
 * Created by dwightguth on 5/27/15.
 */
public class JavaBackendKModule extends AbstractKModule {

    @Override
    public List<Module> getKompileModules() {
        List<Module> mods = super.getKompileModules();
        mods.add(new AbstractModule() {
            @Override
            protected void configure() {

                MapBinder<String, org.kframework.compile.Backend> mapBinder = MapBinder.newMapBinder(
                        binder(), String.class, org.kframework.compile.Backend.class);
                mapBinder.addBinding("java").to(JavaBackend.class);
            }
        });
        return mods;
    }

    @Override
    public List<Module> getKRunModules() {
        return Collections.singletonList(new AbstractModule() {
            @Override
            protected void configure() {

                MapBinder<String, Function<org.kframework.definition.Module, Rewriter>> rewriterBinder = MapBinder.newMapBinder(
                        binder(), TypeLiteral.get(String.class), new TypeLiteral<Function<org.kframework.definition.Module, Rewriter>>() {
                        });
                rewriterBinder.addBinding("java").to(InitializeRewriter.class);

                MapBinder<String, Integer> checkPointBinder = MapBinder.newMapBinder(
                        binder(), String.class, Integer.class, Names.named("checkpointIntervalMap"));
                checkPointBinder.addBinding("java").toInstance(50); //TODO(dwightguth): finesse this number

                MapBinder<ToolActivation, ExecutionMode> executionBinder = MapBinder.newMapBinder(binder(),
                        ToolActivation.class, ExecutionMode.class);

                executionBinder.addBinding(new ToolActivation.OptionActivation("--prove")).to(ProofExecutionMode.class);
            }
        });
    }

    @Override
    public List<Module> getDefinitionSpecificKEqModules() {
        return Collections.singletonList(new AbstractModule() {
            @Override
            protected void configure() {

                MapBinder<String, Function<org.kframework.definition.Module, Rewriter>> rewriterBinder = MapBinder.newMapBinder(
                        binder(), TypeLiteral.get(String.class), new TypeLiteral<Function<org.kframework.definition.Module, Rewriter>>() {
                        });
                rewriterBinder.addBinding("java").to(InitializeRewriter.class);

            }
        });
    }
}

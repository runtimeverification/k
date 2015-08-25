// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.Rewriter;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.AbstractKModule;
import org.kframework.transformation.ToolActivation;

import java.util.Collections;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Created by dwightguth on 5/27/15.
 */
public class OcamlBackendKModule extends AbstractKModule {

    @Override
    public List<Pair<Class<?>, Boolean>> kompileOptions() {
        return Collections.singletonList(Pair.of(OcamlOptions.class, true));
    }

    @Override
    public List<Pair<Class<?>, Boolean>> krunOptions() {
        return Collections.singletonList(Pair.of(OcamlKRunOptions.class, true));
    }

    @Override
    public List<Module> getKompileModules() {
        List<Module> mods = super.getKompileModules();
        mods.add(new AbstractModule() {
            @Override
            protected void configure() {

                MapBinder<String, Consumer<CompiledDefinition>> mapBinder = MapBinder.newMapBinder(
                        binder(), TypeLiteral.get(String.class), new TypeLiteral<Consumer<CompiledDefinition>>() {
                        });
                mapBinder.addBinding("ocaml").to(OcamlBackend.class);
            }
        });
        return mods;
    }

    @Override
    public List<Module> getDefinitionSpecificKRunModules() {
        return Collections.singletonList(new AbstractModule() {
            @Override
            protected void configure() {

                MapBinder<String, Function<org.kframework.definition.Module, Rewriter>> rewriterBinder = MapBinder.newMapBinder(
                        binder(), TypeLiteral.get(String.class), new TypeLiteral<Function<org.kframework.definition.Module, Rewriter>>() {
                        });
                rewriterBinder.addBinding("ocaml").to(OcamlRewriter.class);

                MapBinder<ToolActivation, ExecutionMode> executionBinder = MapBinder.newMapBinder(binder(),
                        ToolActivation.class, ExecutionMode.class);

                executionBinder.addBinding(new ToolActivation.OptionActivation("--ocaml-compile")).to(OcamlCompileExecutionMode.class);
            }
        });
    }
}

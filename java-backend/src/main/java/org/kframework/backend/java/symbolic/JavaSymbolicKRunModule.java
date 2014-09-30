// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.io.File;
import java.util.List;

import org.kframework.backend.java.builtins.BuiltinIOOperations;
import org.kframework.backend.java.builtins.BuiltinIOOperationsImpl;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KilFactory;
import org.kframework.backend.java.ksimulation.Simulator;
import org.kframework.backend.java.ksimulation.Waitor;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.tools.Executor;
import org.kframework.krun.tools.Prover;
import org.kframework.transformation.ToolActivation;
import org.kframework.transformation.Transformation;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.Spec;

import com.beust.jcommander.JCommander;
import com.google.common.base.Optional;
import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.PrivateModule;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;

public class JavaSymbolicKRunModule extends AbstractModule {

    private final JavaExecutionOptions options;

    public JavaSymbolicKRunModule(JavaExecutionOptions options) {
        this.options = options;
    }

    @Override
    protected void configure() {

        bind(JavaExecutionOptions.class).toInstance(options);
        bind(Boolean.class).annotatedWith(FreshRules.class).toInstance(false);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().toInstance(options);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(JavaExecutionOptions.class);

        MapBinder<ToolActivation, Transformation<Void, KRunResult<?>>> krunResultTools = MapBinder.newMapBinder(
                binder(), TypeLiteral.get(ToolActivation.class), new TypeLiteral<Transformation<Void, KRunResult<?>>>() {});
        krunResultTools.addBinding(new ToolActivation.OptionActivation("--simulation")).to(Simulator.class);

    }

    public static class CommonModule extends AbstractModule {

        @Override
        protected void configure() {
            install(new JavaSymbolicCommonModule());
            bind(BuiltinIOOperations.class).to(BuiltinIOOperationsImpl.class);

            bind(SymbolicRewriter.class);
            bind(KilFactory.class);
            bind(GlobalContext.class);

            MapBinder<String, Prover> proverBinder = MapBinder.newMapBinder(
                    binder(), String.class, Prover.class);
            proverBinder.addBinding("java").to(JavaSymbolicProver.class);

            MapBinder<String, Executor> executorBinder = MapBinder.newMapBinder(
                    binder(), String.class, Executor.class);
            executorBinder.addBinding("java").to(JavaSymbolicExecutor.class);
        }

        @Provides @Singleton
        Definition javaDefinition(BinaryLoader loader, Context context) {
            Definition def = loader.loadOrDie(Definition.class,
                    new File(context.kompiled, JavaSymbolicBackend.DEFINITION_FILENAME).toString());
            def.setContext(context);
            return def;
        }
    }

    public static class SimulationModule extends PrivateModule {

        private final List<Module> definitionSpecificModules;

        public SimulationModule(List<Module> definitionSpecificModules) {
            this.definitionSpecificModules = definitionSpecificModules;
        }

        @Override
        protected void configure() {
            for (Module m : definitionSpecificModules) {
                install(m);
            }

            bind(Term.class).annotatedWith(Spec.class).to(Term.class);
            bind(SymbolicRewriter.class).annotatedWith(Spec.class).to(SymbolicRewriter.class);
            bind(GlobalContext.class).annotatedWith(Spec.class).to(GlobalContext.class);
            bind(KilFactory.class).annotatedWith(Spec.class).to(KilFactory.class);
            bind(Context.class).annotatedWith(Spec.class).to(Context.class);

            bind(Simulator.class).annotatedWith(Main.class).to(Simulator.class);

            expose(SymbolicRewriter.class).annotatedWith(Spec.class);
            expose(GlobalContext.class).annotatedWith(Spec.class);
            expose(KilFactory.class).annotatedWith(Spec.class);
            expose(Term.class).annotatedWith(Spec.class);
            expose(Context.class).annotatedWith(Spec.class);

            expose(Simulator.class).annotatedWith(Main.class);

            expose(new TypeLiteral<Optional<Waitor>>() {});
        }

        @Provides
        ConfigurationCreationOptions ccOptions(KRunOptions options) {
            ConfigurationCreationOptions simulationCCOptions = new ConfigurationCreationOptions();
            new JCommander(simulationCCOptions,
                    options.experimental.simulation.toArray(
                            new String[options.experimental.simulation.size()]));
            return simulationCCOptions;
        }

        @Provides
        Optional<Waitor> waitor(Waitor waitor) {
            return Optional.of(waitor);
        }
    }
}

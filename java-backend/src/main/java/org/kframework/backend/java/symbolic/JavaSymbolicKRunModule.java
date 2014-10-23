// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.List;

import org.kframework.backend.java.builtins.BuiltinIOOperations;
import org.kframework.backend.java.builtins.BuiltinIOOperationsImpl;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.ksimulation.Simulator;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.tools.Executor;
import org.kframework.krun.tools.Prover;
import org.kframework.transformation.ToolActivation;
import org.kframework.transformation.Transformation;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.Spec;

import com.beust.jcommander.JCommander;
import com.google.inject.AbstractModule;
import com.google.inject.Binding;
import com.google.inject.Key;
import com.google.inject.Module;
import com.google.inject.PrivateModule;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import com.google.inject.spi.DefaultElementVisitor;
import com.google.inject.spi.Element;
import com.google.inject.spi.Elements;

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
            bind(GlobalContext.class);

            MapBinder<String, Prover> proverBinder = MapBinder.newMapBinder(
                    binder(), String.class, Prover.class);
            proverBinder.addBinding("java").to(JavaSymbolicProver.class);

            MapBinder<String, Executor> executorBinder = MapBinder.newMapBinder(
                    binder(), String.class, Executor.class);
            executorBinder.addBinding("java").to(JavaSymbolicExecutor.class);
        }

        @Provides @Singleton
        Definition javaDefinition(BinaryLoader loader, Context context, FileUtil files, KExceptionManager kem) {
            Definition def = loader.loadOrDie(Definition.class,
                    files.resolveKompiled(JavaSymbolicBackend.DEFINITION_FILENAME));
            def.setContext(context);
            def.setKem(kem);
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
            for (Element element : Elements.getElements(definitionSpecificModules)) {
                element.acceptVisitor(new DefaultElementVisitor<Void>() {
                    @Override
                    public <T> Void visit(Binding<T> binding) {
                        Key<T> key = binding.getKey();
                        if (key.getAnnotation() == null && key.getAnnotationType() == null) {
                            bind(key.getTypeLiteral()).annotatedWith(Spec.class).to(key.getTypeLiteral());
                            expose(key.getTypeLiteral()).annotatedWith(Spec.class);
                        }
                        return null;
                    }
                });
            }
            for (Module m : definitionSpecificModules) {
                install(m);
            }

            bind(Simulator.class).annotatedWith(Main.class).to(Simulator.class);
            expose(Simulator.class).annotatedWith(Main.class);
        }

        @Provides
        ConfigurationCreationOptions ccOptions(KRunOptions options) {
            ConfigurationCreationOptions simulationCCOptions = new ConfigurationCreationOptions();
            new JCommander(simulationCCOptions,
                    options.experimental.simulation.toArray(
                            new String[options.experimental.simulation.size()]));
            return simulationCCOptions;
        }
    }
}

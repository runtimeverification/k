// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.io.File;

import org.kframework.backend.java.builtins.BuiltinIOOperations;
import org.kframework.backend.java.builtins.BuiltinIOOperationsImpl;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KilFactory;
import org.kframework.backend.java.ksimulation.Waitor;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.KRunModule.CommonModule;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.KRun;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.Spec;
import com.beust.jcommander.JCommander;
import com.google.common.base.Optional;
import com.google.inject.AbstractModule;
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
        install(new JavaSymbolicCommonModule());

        bind(JavaExecutionOptions.class).toInstance(options);
        bind(Boolean.class).annotatedWith(FreshRules.class).toInstance(false);
        bind(BuiltinIOOperations.class).to(BuiltinIOOperationsImpl.class);

        MapBinder<String, KRun> krunBinder = MapBinder.newMapBinder(
                binder(), String.class, KRun.class);
        krunBinder.addBinding("java").to(JavaSymbolicKRun.class);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().toInstance(options);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(JavaExecutionOptions.class);
    }

    @Provides @Singleton
    Definition javaDefinition(BinaryLoader loader, Context context) {
        Definition def = loader.loadOrDie(Definition.class,
                new File(context.kompiled, JavaSymbolicBackend.DEFINITION_FILENAME).toString());
        return def;
    }

    public static class MainExecutionContextModule extends PrivateModule {

        private final KRunOptions options;

        public MainExecutionContextModule(KRunOptions options) {
            this.options = options;
        }

        @Override
        protected void configure() {
            install(new CommonModule());

            bind(ConfigurationCreationOptions.class).toInstance(options.configurationCreation);

            bind(Term.class).annotatedWith(Main.class).to(Term.class);
            bind(SymbolicRewriter.class).annotatedWith(Main.class).to(SymbolicRewriter.class);
            bind(GlobalContext.class).annotatedWith(Main.class).to(GlobalContext.class);
            bind(KilFactory.class).annotatedWith(Main.class).to(KilFactory.class);
            bind(KRun.class).annotatedWith(Main.class).to(KRun.class);
            bind(Context.class).annotatedWith(Main.class).to(Context.class);

            expose(Term.class).annotatedWith(Main.class);
            expose(SymbolicRewriter.class).annotatedWith(Main.class);
            expose(GlobalContext.class).annotatedWith(Main.class);
            expose(KilFactory.class).annotatedWith(Main.class);
            expose(KRun.class).annotatedWith(Main.class);
            expose(Context.class).annotatedWith(Main.class);
        }
    }

    public static class SimulationModule extends PrivateModule {

        @Override
        protected void configure() {
            install(new CommonModule());

            bind(Term.class).annotatedWith(Spec.class).to(Term.class);
            bind(SymbolicRewriter.class).annotatedWith(Spec.class).to(SymbolicRewriter.class);
            bind(GlobalContext.class).annotatedWith(Spec.class).to(GlobalContext.class);
            bind(KilFactory.class).annotatedWith(Spec.class).to(KilFactory.class);
            bind(Context.class).annotatedWith(Spec.class).to(Context.class);

            expose(SymbolicRewriter.class).annotatedWith(Spec.class);
            expose(GlobalContext.class).annotatedWith(Spec.class);
            expose(KilFactory.class).annotatedWith(Spec.class);
            expose(Term.class).annotatedWith(Spec.class);
            expose(Context.class).annotatedWith(Spec.class);

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

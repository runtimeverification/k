// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.io.File;
import java.util.Map;

import org.kframework.backend.java.builtins.BuiltinIOOperations;
import org.kframework.backend.java.builtins.RealBuiltinIOOperations;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KilFactory;
import org.kframework.backend.java.ksimulation.Waitor;
import org.kframework.backend.java.symbolic.FreshRules;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.JavaSymbolicBackend;
import org.kframework.backend.java.symbolic.JavaSymbolicCommonModule;
import org.kframework.backend.java.symbolic.SymbolicRewriter;
import org.kframework.kil.Configuration;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.InitialConfigurationProvider;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.KRun;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Spec;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import com.beust.jcommander.JCommander;
import com.google.common.base.Optional;
import com.google.inject.AbstractModule;
import com.google.inject.PrivateModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;

public class KRunModule extends AbstractModule {

    private final KRunOptions options;

    public KRunModule(KRunOptions options) {
        this.options = options;
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KRunFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KRUN);
        bind(KRunOptions.class).toInstance(options);
        bind(SMTOptions.class).toInstance(options.experimental.smt);
        bind(GlobalOptions.class).toInstance(options.global);
        bind(ColorOptions.class).toInstance(options.color);
        bind(JavaExecutionOptions.class).toInstance(options.experimental.javaExecution);
        bind(Boolean.class).annotatedWith(FreshRules.class).toInstance(false);
    }

    public static class CommonModule extends AbstractModule {

        @Override
        protected void configure() {
            install(new DefinitionLoadingModule());
            install(new JavaSymbolicCommonModule());

            MapBinder<KompileOptions.Backend, KRun> krunBinder = MapBinder.newMapBinder(
                    binder(), KompileOptions.Backend.class, KRun.class);
            for (KompileOptions.Backend enumVal : KompileOptions.Backend.values()) {
                if (enumVal.generatesDefinition()) {
                    krunBinder.addBinding(enumVal).to(enumVal.krun());
                }
            }

            bind(Term.class).toProvider(InitialConfigurationProvider.class);
            bind(BuiltinIOOperations.class).to(RealBuiltinIOOperations.class);
        }

        @Provides
        DefinitionLoadingOptions defLoadingOptions(ConfigurationCreationOptions options) {
            return options.definitionLoading;
        }

        @Provides
        KRun getKRun(KompileOptions options, Map<KompileOptions.Backend, Provider<KRun>> map) {
            return map.get(options.backend).get();
        }

        @Provides @Singleton
        Configuration configuration(BinaryLoader loader, Context context, Stopwatch sw) {
            Configuration cfg = loader.loadOrDie(Configuration.class,
                    new File(context.kompiled, "configuration.bin").getAbsolutePath());
            sw.printIntermediate("Reading configuration from binary");
            return cfg;
        }

        @Provides @Singleton
        Definition javaDefinition(BinaryLoader loader, Context context) {
            Definition def = loader.loadOrDie(Definition.class,
                    new File(context.kompiled, JavaSymbolicBackend.DEFINITION_FILENAME).toString());
            return def;
        }
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

    public static class NoSimulationModule extends AbstractModule {

        private final KRunOptions options;

        public NoSimulationModule(KRunOptions options) {
            this.options = options;
        }

        @Override
        protected void configure() {
            install(new CommonModule());
            bind(new TypeLiteral<Optional<Waitor>> () {})
                .toInstance(Optional.<Waitor>absent());

            bind(ConfigurationCreationOptions.class).toInstance(options.configurationCreation);
            bind(Term.class).annotatedWith(Main.class).to(Term.class);
            bind(KRun.class).annotatedWith(Main.class).to(KRun.class);
            bind(Context.class).annotatedWith(Main.class).to(Context.class);
        }
    }
}

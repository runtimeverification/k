// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.backend.java.ksimulation.Waitor;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.KRun;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.First;
import org.kframework.utils.inject.Second;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import com.beust.jcommander.JCommander;
import com.google.common.base.Optional;
import com.google.inject.AbstractModule;
import com.google.inject.PrivateModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;

public class KRunModule extends AbstractModule {

    private final KRunOptions options;

    public KRunModule(KRunOptions options) {
        this.options = options;
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KRunFrontEnd.class);
        bind(KRunOptions.class).toInstance(options);
        bind(SMTOptions.class).toInstance(options.experimental.smt);
        bind(GlobalOptions.class).toInstance(options.global);
        bind(ColorOptions.class).toInstance(options.color);
        bind(JavaExecutionOptions.class).toInstance(options.experimental.javaExecution);
    }

    @Provides
    DefinitionLoadingOptions defLoadingOptions(ConfigurationCreationOptions options) {
        return options.definitionLoading;
    }

    public static class MainExecutionContextModule extends PrivateModule {

        private final KRunOptions options;

        public MainExecutionContextModule(KRunOptions options) {
            this.options = options;
        }

        @Override
        protected void configure() {
            install(new DefinitionLoadingModule());

            bind(ConfigurationCreationOptions.class).toInstance(options.configurationCreation);

            bind(Term.class).annotatedWith(First.class).to(Term.class);
            bind(JavaSymbolicKRun.class).annotatedWith(First.class).to(JavaSymbolicKRun.class);
            bind(KRun.class).annotatedWith(First.class).to(KRun.class);
            bind(Context.class).annotatedWith(First.class).to(Context.class);

            expose(Term.class).annotatedWith(First.class);
            expose(JavaSymbolicKRun.class).annotatedWith(First.class);
            expose(KRun.class).annotatedWith(First.class);
            expose(Context.class).annotatedWith(First.class);
        }
    }

    public static class SimulationModule extends PrivateModule {

        @Override
        protected void configure() {
            install(new DefinitionLoadingModule());

            bind(Term.class).annotatedWith(Second.class).to(Term.class);
            bind(JavaSymbolicKRun.class).annotatedWith(Second.class).to(JavaSymbolicKRun.class);
            bind(Context.class).annotatedWith(Second.class).to(Context.class);

            expose(JavaSymbolicKRun.class).annotatedWith(Second.class);
            expose(Term.class).annotatedWith(Second.class);
            expose(Context.class).annotatedWith(Second.class);

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
            install(new DefinitionLoadingModule());
            bind(new TypeLiteral<Optional<Waitor>> () {})
                .toInstance(Optional.<Waitor>absent());

            bind(ConfigurationCreationOptions.class).toInstance(options.configurationCreation);
            bind(Term.class).annotatedWith(First.class).to(Term.class);
            bind(KRun.class).annotatedWith(First.class).to(KRun.class);
            bind(Context.class).annotatedWith(First.class).to(Context.class);
        }
    }
}

// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.io.File;
import java.util.Map;

import org.kframework.backend.Backends;
import org.kframework.backend.maude.krun.MaudeKRun;
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
import org.kframework.utils.inject.Options;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import com.google.inject.AbstractModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;

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

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().toInstance(options);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(KRunOptions.Experimental.class);
        experimentalOptionsBinder.addBinding().toInstance(SMTOptions.class);
    }

    public static class CommonModule extends AbstractModule {

        @Override
        protected void configure() {
            install(new DefinitionLoadingModule());

            MapBinder<String, KRun> krunBinder = MapBinder.newMapBinder(
                    binder(), String.class, KRun.class);
            krunBinder.addBinding(Backends.MAUDE).to(MaudeKRun.class);
            krunBinder.addBinding(Backends.SYMBOLIC).to(MaudeKRun.class);

            bind(Term.class).toProvider(InitialConfigurationProvider.class);
        }

        @Provides
        DefinitionLoadingOptions defLoadingOptions(ConfigurationCreationOptions options) {
            return options.definitionLoading;
        }

        @Provides
        KRun getKRun(KompileOptions options, Map<String, Provider<KRun>> map) {
            return map.get(options.backend).get();
        }

        @Provides @Singleton
        Configuration configuration(BinaryLoader loader, Context context, Stopwatch sw) {
            Configuration cfg = loader.loadOrDie(Configuration.class,
                    new File(context.kompiled, "configuration.bin").getAbsolutePath());
            sw.printIntermediate("Reading configuration from binary");
            return cfg;
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

            bind(ConfigurationCreationOptions.class).toInstance(options.configurationCreation);
            bind(Term.class).annotatedWith(Main.class).to(Term.class);
            bind(KRun.class).annotatedWith(Main.class).to(KRun.class);
            bind(Context.class).annotatedWith(Main.class).to(Context.class);
        }
    }
}

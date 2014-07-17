// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import java.io.File;
import java.util.Map;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.symbolic.JavaSymbolicBackend;
import org.kframework.kil.Configuration;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.InitialConfigurationProvider;
import org.kframework.krun.api.KRun;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.options.DefinitionLoadingOptions;

import com.google.inject.AbstractModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.inject.multibindings.MapBinder;

public class DefinitionLoadingModule extends AbstractModule {

    @Override
    protected void configure() {
        MapBinder<KompileOptions.Backend, KRun> mapBinder = MapBinder.newMapBinder(
                binder(), KompileOptions.Backend.class, KRun.class);
        for (KompileOptions.Backend enumVal : KompileOptions.Backend.values()) {
            if (enumVal.generatesDefinition()) {
                mapBinder.addBinding(enumVal).to(enumVal.krun());
            }
        }

        bind(Term.class).toProvider(InitialConfigurationProvider.class);
    }

    @Provides @Singleton
    Context context(BinaryLoader loader, DefinitionLoadingOptions options, GlobalOptions global, Stopwatch sw) {
        Context context = loader.loadOrDie(Context.class, new File(options.definition(),
                "context.bin").getAbsolutePath());

        sw.printIntermediate("Loading serialized context");

        context.dotk = new File(
                options.definition().getParent() + File.separator
                        + ".k");
        if (!context.dotk.exists()) {
            context.dotk.mkdirs();
        }
        context.kompiled = options.definition();

        sw.printIntermediate("Initializing definition paths");
        return context;
    }

    @Provides
    KompileOptions kompileOptions(Context context) {
        return context.kompileOptions;
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

// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kdoc;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import org.kframework.backend.PosterBackend;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.OuterParsingModule;
import org.kframework.utils.options.OuterParsingOptions;

import java.util.Map;

public class KDocModule extends AbstractModule {

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KDocFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KDOC);

        install(new OuterParsingModule());

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KDocOptions.class);
        Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);

        MapBinder<String, PosterBackend> posterBinder = MapBinder.newMapBinder(
                binder(), String.class, PosterBackend.class);
    }

    @Provides
    GlobalOptions globalOptions(KDocOptions options) {
        return options.global;
    }

    @Provides
    OuterParsingOptions outerParsingOptions(KDocOptions options) {
        return options.outerParsing;
    }

    @Provides
    PosterBackend getBackend(KDocOptions options, Map<String, PosterBackend> map, KExceptionManager kem) {
        PosterBackend backend = map.get(options.format);
        if (backend == null) {
            throw KEMException.criticalError("Invalid poster format: " + options.format
                    + ". It should be one of " + map.keySet());
        }
        return backend;
    }

}

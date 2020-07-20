// Copyright (c) 2020 K Team. All Rights Reserved.
package org.kframework.ksearchpattern;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;
import org.kframework.kdoc.KDocOptions;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.DefinitionLoadingOptions;

/**
 * Guice module for k-compile-search-pattern tool.
 *
 * Binds the information needed to compute the kompiled directory as well as the options
 * and frontend.
 */
public class KSearchPatternModule extends AbstractModule {
    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KSearchPatternFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KSEARCHPATTERN);

        install(new DefinitionLoadingModule());

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KSearchPatternOptions.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
    }

    @Provides @RequestScoped
    GlobalOptions globalOptions(KSearchPatternOptions options) {
        return options.global;
    }

    @Provides
    DefinitionLoadingOptions defLoadingOptions(KSearchPatternOptions options) {
        return options.definitionLoading;
    }
}

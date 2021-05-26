// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kast;

import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.unparser.PrintOptions;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.DefinitionLoadingOptions;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;

public class KastModule extends AbstractModule {

    @Override
    public void configure() {
        bind(FrontEnd.class).to(KastFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KAST);

        install(new DefinitionLoadingModule());

        bind(Context.class).annotatedWith(Main.class).to(Context.class);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KastOptions.class);
    }

    @Provides @RequestScoped
    GlobalOptions globalOptions(KastOptions options) {
        return options.global;
    }

    @Provides @RequestScoped
    PrintOptions printOptions(KastOptions options) {
        return options.print;
    }

    @Provides
    DefinitionLoadingOptions defLoadingOptions(KastOptions options) {
        return options.definitionLoading;
    }
}

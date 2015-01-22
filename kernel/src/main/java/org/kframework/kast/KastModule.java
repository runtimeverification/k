// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kast;

import org.kframework.kil.loader.Context;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.options.DefinitionLoadingOptions;
import com.google.inject.AbstractModule;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;

public class KastModule extends AbstractModule {

    private final KastOptions options;

    public KastModule(KastOptions options) {
        this.options = options;
    }

    @Override
    public void configure() {
        bind(FrontEnd.class).to(KastFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KAST);
        bind(KastOptions.class).toInstance(options);
        bind(GlobalOptions.class).toInstance(options.global);
        bind(DefinitionLoadingOptions.class).toInstance(options.definitionLoading);

        install(new DefinitionLoadingModule());

        bind(Context.class).annotatedWith(Main.class).to(Context.class);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().toInstance(options);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(KastOptions.Experimental.class);
    }
}

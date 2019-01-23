// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kdep;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;
import org.kframework.kdoc.KDocOptions;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.OuterParsingModule;
import org.kframework.utils.options.OuterParsingOptions;

/**
 * Guice module for kdep tool. Binds the information needed to compute the kompiled directory as well as the options
 * and frontend.
 */
public class KDepModule extends AbstractModule {
    @Override
    protected void configure() {

        bind(FrontEnd.class).to(KDepFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KDEP);

        install(new OuterParsingModule());

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KDepOptions.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
    }

    @Provides
    GlobalOptions globalOptions(KDepOptions options) {
        return options.global;
    }

    @Provides
    OuterParsingOptions outerParsingOptions(KDepOptions options) {
        return options.outerParsing;
    }
}

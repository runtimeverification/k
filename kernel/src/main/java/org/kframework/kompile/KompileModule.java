// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.OuterParsingModule;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.SMTOptions;

import java.util.Map;

public class KompileModule extends AbstractModule {

    public KompileModule() {
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KompileFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KOMPILE);

        install(new OuterParsingModule());
        install(new BackendModule());

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KompileOptions.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(KompileOptions.Experimental.class);
        experimentalOptionsBinder.addBinding().toInstance(SMTOptions.class);
    }

    @Provides
    SMTOptions smtOptions(KompileOptions options) {
        return options.experimental.smt;
    }

    @Provides
    GlobalOptions globalOptions(KompileOptions options) {
        return options.global;
    }

    @Provides
    OuterParsingOptions outerParsingOptions(KompileOptions options) { return options.outerParsing; }

}

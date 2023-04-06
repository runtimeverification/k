// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kbmc;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;
import org.kframework.kompile.BackendModule;
import org.kframework.krun.RewriterModule;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.unparser.PrintOptions;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BackendOptions;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.SMTOptions;

public class KBMCModule extends AbstractModule {
    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KBMCFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KBMC);

        install(new BackendModule());
        install(new RewriterModule());

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KBMCOptions.class);
    }

    @Provides @RequestScoped
    GlobalOptions globalOptions(KBMCOptions options) { return options.global; }

    @Provides @RequestScoped
    OuterParsingOptions outerParsingOptions(KBMCOptions options) { return options.outer; }

    @Provides @RequestScoped
    InnerParsingOptions innerParsingOptions(KBMCOptions options) { return options.inner; }

    @Provides @RequestScoped
    PrintOptions printOptions(KBMCOptions options) {
        return options.print;
    }

    @Provides
    DefinitionLoadingOptions loadingOptions(KBMCOptions options) {
        return options.definitionLoading;
    }

    @Provides
    SMTOptions smtOptions(KBMCOptions options) {
        return options.smt;
    }

    @Provides
    BackendOptions backendOptions(KBMCOptions options) {
        return options.backend;
    }
}


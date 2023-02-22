// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kprovex;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.multibindings.Multibinder;
import org.kframework.kompile.BackendModule;
import org.kframework.kprove.KProveOptions;
import org.kframework.krun.RewriterModule;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.unparser.PrintOptions;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.OuterParsingModule;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BackendOptions;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.SMTOptions;

public class KProveModule extends AbstractModule {
    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KProveFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KPROVE);

        install(new BackendModule());
        install(new RewriterModule());

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KProveOptions.class);
    }

    @Provides @RequestScoped
    GlobalOptions globalOptions(KProveOptions options) {
        return options.getGlobalOptions_useOnlyInGuiceProvider();
    }

    @Provides @RequestScoped
    OuterParsingOptions outerParsingOptions(KProveOptions options) { return options.outerParsing; }

    @Provides @RequestScoped
    InnerParsingOptions InnerParsingOptions(KProveOptions options) { return options.innerParsing; }

    @Provides @RequestScoped
    PrintOptions printOptions(KProveOptions options) {
        return options.print;
    }

    @Provides
    DefinitionLoadingOptions loadingOptions(KProveOptions options) {
        return options.definitionLoading;
    }

    @Provides
    BackendOptions backendOptions(KProveOptions options) {
        return options.backend;
    }

    @Provides
    SMTOptions smtOptions(KProveOptions options) {
        return options.smt;
    }
}

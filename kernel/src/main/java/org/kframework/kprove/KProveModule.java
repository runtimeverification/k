package org.kframework.kprove;

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
import org.kframework.utils.options.DefinitionLoadingOptions;
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
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);

    }

    @Provides
    GlobalOptions globalOptions(KProveOptions options) {
        return options.global;
    }

    @Provides
    PrintOptions printOptions(KProveOptions options) {
        return options.print;
    }

    @Provides
    DefinitionLoadingOptions loadingOptions(KProveOptions options) {
        return options.definitionLoading;
    }

    @Provides
    SMTOptions smtOptions(KProveOptions options) {
        return options.smt;
    }
}

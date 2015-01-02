// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kserver;
import java.io.File;

import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.file.DefinitionDir;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.Options;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;
import com.google.inject.util.Providers;

public class KServerModule extends AbstractModule {

    @Override
    protected void configure() {
        bind(Tool.class).toInstance(Tool.KSERVER);
        bind(FrontEnd.class).to(KServerFrontEnd.class);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KServerOptions.class);
        Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);

        bind(File.class).annotatedWith(DefinitionDir.class).toProvider(Providers.of(null));
        bind(File.class).annotatedWith(KompiledDir.class).toProvider(Providers.of(null));
    }

    @Provides
    GlobalOptions globalOptions(KServerOptions options) {
        return options.global;
    }

}

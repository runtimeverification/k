// Copyright (c) 2014-2016 K Team. All Rights Reserved.
package org.kframework.ktest;

import java.io.File;

import org.kframework.krun.ColorOptions;
import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.file.DefinitionDir;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.RequestScoped;
import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;
import com.google.inject.util.Providers;

public class KTestModule extends AbstractModule {

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KTestFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KTEST);
        bind(KTestOptions.class).in(RequestScoped.class);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KTestOptions.class);
        Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);

        bind(File.class).annotatedWith(DefinitionDir.class).toProvider(Providers.of(null));
        bind(File.class).annotatedWith(KompiledDir.class).toProvider(Providers.of(null));
    }

    @Provides
    GlobalOptions globalOptions(KTestOptions options) {
        return options.getGlobal();
    }

    @Provides
    ColorOptions colorOptions(KTestOptions options) {
        return options.getColorOptions();
    }

}

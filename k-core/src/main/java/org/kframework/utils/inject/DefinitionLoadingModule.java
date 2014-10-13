// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import java.io.File;

import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.options.DefinitionLoadingOptions;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.Singleton;

public class DefinitionLoadingModule extends AbstractModule {

    @Override
    protected void configure() {
    }

    @Provides @Singleton
    Context context(
            BinaryLoader loader,
            DefinitionLoadingOptions options,
            GlobalOptions global,
            Stopwatch sw,
            KExceptionManager kem) {
        Context context = loader.loadOrDie(Context.class, new File(options.definition(),
                "context.bin").getAbsolutePath());

        sw.printIntermediate("Loading serialized context");

        context.kompiled = options.definition();

        sw.printIntermediate("Initializing definition paths");
        return context;
    }

    @Provides
    KompileOptions kompileOptions(Context context) {
        return context.kompileOptions;
    }
}

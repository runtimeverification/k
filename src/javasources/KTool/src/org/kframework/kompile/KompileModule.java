// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import java.util.Map;

import org.kframework.backend.Backend;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.kil.loader.Context;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.options.SMTOptions;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.multibindings.MapBinder;

public class KompileModule extends AbstractModule {

    private final Context context;
    private final KompileOptions options;

    public KompileModule(Context context, KompileOptions options) {
        this.context = context;
        this.options = options;
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KompileFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KOMPILE);
        bind(Context.class).toInstance(context);
        bind(KompileOptions.class).toInstance(options);
        bind(GlobalOptions.class).toInstance(options.global);
        bind(SMTOptions.class).toInstance(options.experimental.smt);
        bind(JavaExecutionOptions.class).toInstance(new JavaExecutionOptions());

        MapBinder<KompileOptions.Backend, Backend> mapBinder = MapBinder.newMapBinder(
                binder(), KompileOptions.Backend.class, Backend.class);
        for (KompileOptions.Backend enumVal : KompileOptions.Backend.values()) {
            mapBinder.addBinding(enumVal).to(enumVal.backend());
        }
    }

    @Provides
    Backend getBackend(KompileOptions options, Map<KompileOptions.Backend, Backend> map) {
        return map.get(options.backend);
    }
}

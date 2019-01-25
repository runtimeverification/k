// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.multibindings.MapBinder;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.compile.Backend;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Map;

public class BackendModule extends AbstractModule {
    @Override
    protected void configure() {
        MapBinder<String, Backend> backendBinder = MapBinder.newMapBinder(
                binder(), String.class, org.kframework.compile.Backend.class);
        backendBinder.addBinding("kore").to(KoreBackend.class);
    }

    @Provides
    org.kframework.compile.Backend getKoreBackend(KompileOptions options, Map<String, Backend> map, KExceptionManager kem) {
        org.kframework.compile.Backend backend = map.get(options.backend);
        if (backend == null) {
            throw KEMException.criticalError("Invalid backend: " + options.backend
                    + ". It should be one of " + map.keySet());
        }
        return backend;
    }
}

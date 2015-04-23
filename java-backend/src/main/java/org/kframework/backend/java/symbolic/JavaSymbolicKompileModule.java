// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.AbstractModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.multibindings.MapBinder;
import org.kframework.backend.Backend;
import org.kframework.backend.java.indexing.IndexingAlgorithm;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;

import java.util.Map;

public class JavaSymbolicKompileModule extends AbstractModule {

    @Override
    protected void configure() {
        bind(Stage.class).toInstance(Stage.INITIALIZING);
        bind(Boolean.class).annotatedWith(FreshRules.class).toInstance(true);
        bind(JavaExecutionOptions.class).toInstance(new JavaExecutionOptions());
        bind(FileSystem.class).to(PortableFileSystem.class);

        MapBinder<IndexingAlgorithm, RuleIndex> indexBinder = MapBinder.newMapBinder(
                binder(), IndexingAlgorithm.class, RuleIndex.class);
        for (IndexingAlgorithm enumVal : IndexingAlgorithm.values()) {
            indexBinder.addBinding(enumVal).to(enumVal.clazz);
        }

        MapBinder<String, Backend> mapBinder = MapBinder.newMapBinder(
                binder(), String.class, Backend.class);
        mapBinder.addBinding("java").to(JavaSymbolicBackend.class);
    }

    @Provides
    RuleIndex getRuleIndex(JavaExecutionOptions options, Map<IndexingAlgorithm, Provider<RuleIndex>> map) {
        return map.get(options.ruleIndex).get();
    }

    @Provides
    Definition definition(GlobalContext context) {
        return context.getDefinition();
    }
}

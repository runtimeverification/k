// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import java.io.File;
import java.util.Map;

import org.kframework.main.Tool;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TempDir;
import org.kframework.utils.file.WorkingDir;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.inject.TypeLiteral;

public class CommonModule extends AbstractModule {

    @Override
    protected void configure() {
        requestStaticInjection(Tool.class);

        bind(File.class).annotatedWith(WorkingDir.class).toInstance(new File("."));
        bind(new TypeLiteral<Map<String, String>>() {}).annotatedWith(Environment.class).toInstance(System.getenv());

        //TODO(dwightguth): when we upgrade to Guice 4.0, add
        //binder().requireAtInjectOnConstructors()
    }

    @Provides @TempDir @Singleton
    File tempDir(@WorkingDir File workingDir, Tool tool) {
        return new File(workingDir, FileUtil.generateUniqueFolderName("." + tool.name().toLowerCase()));
    }

}

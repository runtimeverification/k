// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.file;

import java.io.File;
import java.util.Map;

import com.google.inject.AbstractModule;
import com.google.inject.TypeLiteral;

public class FileSystemModule extends AbstractModule {

    private final File workingDir;
    private final Map<String, String> env;

    public FileSystemModule(File workingDir, @Environment Map<String, String> env) {
        this.workingDir = workingDir;
        this.env = env;
    }

    @Override
    protected void configure() {
        bind(File.class).annotatedWith(WorkingDir.class).toInstance(workingDir);
        bind(new TypeLiteral<Map<String, String>>() {}).annotatedWith(Environment.class).toInstance(env);
    }

}

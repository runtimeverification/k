// Copyright (c) 2014-2015 K Team. All Rights Reserved.
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

public class CommonModule extends AbstractModule {

    @Override
    protected void configure() {}

    @Provides @TempDir @Singleton
    File tempDir(@WorkingDir File workingDir, Tool tool) {
        return new File(workingDir, FileUtil.generateUniqueFolderName("." + tool.name().toLowerCase()));
    }

    @Provides
    ProcessBuilder pb(@WorkingDir File workingDir, @Environment Map<String, String> env) {
        ProcessBuilder pb = new ProcessBuilder().directory(workingDir);
        pb.environment().clear();
        pb.environment().putAll(env);
        return pb;
    }

}

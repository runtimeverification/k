// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.file;

import static org.fusesource.jansi.internal.CLibrary.isatty;

import java.io.File;
import java.util.Map;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
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

    @Provides
    TTYInfo ttyInfo(@Environment Map<String, String> env) {
        boolean stdin, stdout, stderr;
        if (env.containsKey("NAILGUN_TTY_0")) {
            stdin = !env.get("NAILGUN_TTY_0").equals("0");
        } else {
            stdin = isatty(0) != 0;
        }
        if (env.containsKey("NAILGUN_TTY_1")) {
            stdout = !env.get("NAILGUN_TTY_1").equals("0");
        } else {
            stdout = isatty(1) != 0;
        }
        if (env.containsKey("NAILGUN_TTY_2")) {
            stderr = !env.get("NAILGUN_TTY_2").equals("0");
        } else {
            stderr = isatty(2) != 0;
        }
        return new TTYInfo(stdin, stdout, stderr);
    }

}

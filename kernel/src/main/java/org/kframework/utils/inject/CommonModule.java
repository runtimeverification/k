// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static org.fusesource.jansi.internal.CLibrary.isatty;

import java.io.File;
import java.util.Map;

import org.kframework.main.Tool;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import org.kframework.utils.file.TempDir;
import org.kframework.utils.file.WorkingDir;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.name.Names;

public class CommonModule extends AbstractModule {

    @Override
    protected void configure() {
        SimpleScope requestScope = new SimpleScope();
        bindScope(RequestScoped.class, requestScope);
        DefinitionScope definitionScope = new DefinitionScope();
        bindScope(DefinitionScoped.class, definitionScope);
        bind(SimpleScope.class).annotatedWith(Names.named("requestScope")).toInstance(requestScope);
        bind(DefinitionScope.class).toInstance(definitionScope);
        bind(File.class).annotatedWith(WorkingDir.class)
            .toProvider(SimpleScope.seededKeyProvider()).in(RequestScoped.class);;
        bind(new TypeLiteral<Map<String, String>>() {}).annotatedWith(Environment.class)
            .toProvider(SimpleScope.seededKeyProvider()).in(RequestScoped.class);
    }

    @Provides @TempDir @RequestScoped
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

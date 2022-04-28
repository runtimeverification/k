// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.AbstractModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.DefinitionDir;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.WorkingDir;
import org.kframework.utils.options.DefinitionLoadingOptions;

import java.io.File;
import java.io.FilenameFilter;
import java.util.Map;

public class DefinitionLoadingModule extends AbstractModule {

    @Override
    protected void configure() {
    }

    @Provides @DefinitionScoped
    CompiledDefinition koreDefinition(BinaryLoader loader, FileUtil files) {
        return loader.loadOrDie(CompiledDefinition.class, files.resolveKompiled("compiled.bin"));
    }


    @Provides @RequestScoped
    KompileOptions kompileOptions(Provider<CompiledDefinition> compiledDef) {
        // a hack, but it's good enough for what we need from it, which is a temporary solution
        KompileOptions res = compiledDef.get().kompileOptions;
        return res;
    }

    @Provides @KompiledDir
    File directory(DefinitionLoadingOptions options, @WorkingDir File workingDir, @Environment Map<String, String> env) {
        File directory = null;
        if (options.inputDirectory != null) {
            if (options.directory != null)
                throw KEMException.criticalError("Cannot use both --directory and --input-kdir at the same time.");
            File f = new File(options.inputDirectory);
            if (f.isAbsolute()) {
                directory = f;
            } else {
                directory = new File(workingDir, options.inputDirectory);
            }
        } else if (env.get("KRUN_KOMPILED_DIR") != null) {
            File f = new File(env.get("KRUN_KOMPILED_DIR"));
            if (f.isAbsolute()) {
                directory = f;
            } else {
                directory = new File(workingDir, env.get("KRUN_KOMPILED_DIR"));
            }
        } else {
            File whereDir;
            if (options.directory == null) {
                if (env.get("KRUN_COMPILED_DEF") != null) {
                    File f = new File(env.get("KRUN_COMPILED_DEF"));
                    if (f.isAbsolute()) {
                        whereDir = f;
                    } else {
                        whereDir = new File(workingDir, env.get("KRUN_COMPILED_DEF"));
                    }
                } else {
                    whereDir = workingDir;
                }
            } else {
                File f = new File(options.directory);
                if (f.isAbsolute()) {
                    whereDir = f;
                } else {
                    whereDir = new File(workingDir, options.directory);
                }
            }
            File[] dirs = whereDir.listFiles((current, name) -> new File(current, name).isDirectory());

            if (dirs != null) {
                for (File dir : dirs) {
                    if (dir.getAbsolutePath().endsWith("-kompiled")) {
                        if (directory != null) {
                            throw KEMException.criticalError("Multiple compiled definitions found in the "
                                    + "current working directory: " + directory.getAbsolutePath() + " and " +
                                    dir.getAbsolutePath());
                        } else {
                            directory = dir;
                        }
                    }
                }
            }

            if (directory == null) {
                throw KEMException.criticalError("Could not find a compiled definition. " +
                        "Use --directory or --input-kdir to specify one.");
            }
        }
        if (!directory.isDirectory()) {
            throw KEMException.criticalError("Does not exist or not a directory: " + directory.getAbsolutePath());
        }
        return directory;
    }
}

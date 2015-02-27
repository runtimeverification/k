// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kdoc;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.PosterBackend;
import org.kframework.kil.Definition;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.Concrete;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;


public class KDocFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KDocModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }

    private final Provider<PosterBackend> backend;
    private final Provider<Definition> def;
    private final DefinitionScope scope;
    private final Provider<File> kompiledDir;

    @Inject
    public KDocFrontEnd(
            KExceptionManager kem,
            GlobalOptions globalOptions,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo,
            Provider<PosterBackend> backend,
            @Concrete Provider<Definition> def,
            FileUtil files,
            DefinitionScope scope,
            @KompiledDir Provider<File> kompiledDir) {
        super(kem, globalOptions, usage, experimentalUsage, jarInfo, files);
        this.backend = backend;
        this.def = def;
        this.scope = scope;
        this.kompiledDir = kompiledDir;
    }

    @Override
    protected int run() {
        scope.enter(kompiledDir.get());
        try {
            backend.get().run(def.get());
            return 0;
        } finally {
            scope.exit();
        }
    }

}

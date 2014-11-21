// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kdoc;
import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.PosterBackend;
import org.kframework.kil.Definition;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;


public class KDocFrontEnd extends FrontEnd {

    public static List<Module> getModules(String[] args) {
        KDocOptions options = new KDocOptions();

        List<Module> modules = new ArrayList<>();
        modules.add(new KDocModule(options));
        modules.add(new JCommanderModule(args));
        modules.add(new CommonModule());
        return modules;
    }

    private final PosterBackend backend;
    private final Provider<Definition> def;

    @Inject
    public KDocFrontEnd(
            KExceptionManager kem,
            GlobalOptions globalOptions,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo,
            PosterBackend backend,
            Provider<Definition> def,
            FileUtil files) {
        super(kem, globalOptions, usage, experimentalUsage, jarInfo, files);
        this.backend = backend;
        this.def = def;
    }

    @Override
    protected boolean run() {
        backend.run(def.get());
        return true;
    }

}

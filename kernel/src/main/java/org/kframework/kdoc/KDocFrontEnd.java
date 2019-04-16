// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kdoc;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.backend.PosterBackend;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import java.util.ArrayList;
import java.util.List;


public class KDocFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KDocModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }

    private final KDocOptions options;
    private final Provider<PosterBackend> backend;

    @Inject
    public KDocFrontEnd(
            KDocOptions options,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo,
            Provider<FileUtil> files,
            Provider<PosterBackend> backend) {
        super(kem, globalOptions, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.backend = backend;
    }

    @Override
    protected int run() {
        return 0;
    }

}

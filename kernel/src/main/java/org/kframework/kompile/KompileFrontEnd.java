// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.compile.Backend;
import org.kframework.main.FrontEnd;
import org.kframework.parser.concrete2kore.ParseCache;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class KompileFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KompileModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }


    private final KompileOptions options;
    private final Provider<Backend> koreBackend;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final BinaryLoader loader;
    private final Provider<FileUtil> files;
    private final Provider<DefinitionStorage> definitionStorage;

    @Inject
    KompileFrontEnd(
            KompileOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Provider<Backend> koreBackend,
            Stopwatch sw,
            KExceptionManager kem,
            BinaryLoader loader,
            JarInfo jarInfo,
            Provider<FileUtil> files,
            Provider<DefinitionStorage> definitionStorage) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.koreBackend = koreBackend;
        this.sw = sw;
        this.kem = kem;
        this.loader = loader;
        this.files = files;
        this.definitionStorage = definitionStorage;
    }

    @Override
    public int run() {
        if (!options.outerParsing.mainDefinitionFile(files.get()).exists()) {
            throw KEMException.criticalError("Definition file doesn't exist: " +
                    options.outerParsing.mainDefinitionFile(files.get()).getAbsolutePath());
        }

        Backend backend = koreBackend.get();
        DefinitionStorage definitionStorage = this.definitionStorage.get();
        Map<String, ParseCache> caches = definitionStorage.loadParseCaches(options);
        Kompile kompile = new Kompile(options, files.get(), kem, sw, caches);
        CompiledDefinition def = null;
        try {
            def = kompile
                    .run(options.outerParsing.mainDefinitionFile(files.get()), options.mainModule(files.get()), options.syntaxModule(files.get()), backend.steps(), backend.excludedModuleTags());
        } finally {
            sw.printIntermediate("Kompile to kore");
            final DefinitionAndCache definitionAndCache = new DefinitionAndCache(def, caches);
            definitionStorage.save(definitionAndCache, options);
            sw.printIntermediate("Save to disk");
        }
        backend.accept(def);
        sw.printIntermediate("Backend");
        loader.saveOrDie(files.get().resolveKompiled("timestamp"), "");
        sw.printTotal("Total");
        return 0;
    }
}


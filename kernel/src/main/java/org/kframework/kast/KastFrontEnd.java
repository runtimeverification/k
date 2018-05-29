// Copyright (c) 2012-2018 K Team. All Rights Reserved.
package org.kframework.kast;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.attributes.Source;
import org.kframework.compile.ExpandMacros;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.main.FrontEnd;
import org.kframework.parser.outer.Outer;
import org.kframework.unparser.ToKast;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import scala.Option;

import java.io.File;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class KastFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KastModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }

    private final KastOptions options;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final FileUtil files;
    private final Map<String, String> env;
    private final Provider<File> kompiledDir;
    private final Provider<CompiledDefinition> compiledDef;
    private final DefinitionScope scope;

    @Inject
    KastFrontEnd(
            KastOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Stopwatch sw,
            KExceptionManager kem,
            JarInfo jarInfo,
            @Environment Map<String, String> env,
            FileUtil files,
            @KompiledDir Provider<File> kompiledDir,
            Provider<CompiledDefinition> compiledDef,
            DefinitionScope scope) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.sw = sw;
        this.kem = kem;
        this.files = files;
        this.env = env;
        this.kompiledDir = kompiledDir;
        this.compiledDef = compiledDef;
        this.scope = scope;
    }

    /**
     *
     * @return true if the application terminated normally; false otherwise
     */
    @Override
    public int run() {
        scope.enter(kompiledDir.get());
        try {
            Reader stringToParse = options.stringToParse();
            Source source = options.source();

            CompiledDefinition def = compiledDef.get();
            org.kframework.kore.Sort sort = options.sort;
            if (sort == null) {
                if (env.get("KRUN_SORT") != null) {
                    sort = Outer.parseSort(env.get("KRUN_SORT"));
                } else {
                    sort = def.programStartSymbol;
                }
            }
            org.kframework.definition.Module mod;
            org.kframework.definition.Module compiledMod;
            if (options.module == null) {
                mod = def.programParsingModuleFor(def.mainSyntaxModuleName(), kem).get();
                compiledMod = def.kompiledDefinition.getModule(def.mainSyntaxModuleName()).get();
            } else {
                Option<org.kframework.definition.Module> mod2 = def.programParsingModuleFor(options.module, kem);
                if (mod2.isEmpty()) {
                    throw KEMException.innerParserError("Module " + options.module + " not found. Specify a module with -m.");
                }
                mod = mod2.get();
                compiledMod = def.kompiledDefinition.getModule(options.module).get();
            }
            K parsed = def.getParser(mod, sort, kem).apply(FileUtil.read(stringToParse), source);
            if (options.expandMacros) {
                parsed = new ExpandMacros(compiledMod, kem, files, options.global, def.kompileOptions).expand(parsed);
            }
            System.out.println(ToKast.apply(parsed));
            sw.printTotal("Total");
            return 0;
        } finally {
            scope.exit();
        }
    }
}

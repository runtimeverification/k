// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kast;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.attributes.Source;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.main.FrontEnd;
import org.kframework.parser.KRead;
import org.kframework.parser.outer.Outer;
import org.kframework.unparser.KPrint;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.TTYInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.Stopwatch;
import scala.Option;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Properties;

public class KastFrontEnd extends FrontEnd {

    public static List<com.google.inject.Module> getModules() {
        List<com.google.inject.Module> modules = new ArrayList<>();
        modules.add(new KastModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }

    private final KastOptions options;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final Provider<FileUtil> files;
    private final Map<String, String> env;
    private final Provider<File> kompiledDir;
    private final Provider<CompiledDefinition> compiledDef;
    private final DefinitionScope scope;
    private final TTYInfo ttyInfo;

    @Inject
    KastFrontEnd(
            KastOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Stopwatch sw,
            KExceptionManager kem,
            JarInfo jarInfo,
            @Environment Map<String, String> env,
            Provider<FileUtil> files,
            @KompiledDir Provider<File> kompiledDir,
            Provider<CompiledDefinition> compiledDef,
            DefinitionScope scope,
            TTYInfo ttyInfo
            ) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.sw = sw;
        this.kem = kem;
        this.files = files;
        this.env = env;
        this.kompiledDir = kompiledDir;
        this.compiledDef = compiledDef;
        this.scope = scope;
        this.ttyInfo = ttyInfo;
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
            KPrint kprint = new KPrint(kem, files.get(), ttyInfo, options.print, compiledDef.get().kompileOptions);
            KRead kread = new KRead(kem, files.get());

            org.kframework.kore.Sort sort = options.sort;
            if (sort == null) {
                if (env.get("KRUN_SORT") != null) {
                    sort = Outer.parseSort(env.get("KRUN_SORT"));
                } else {
                    sort = def.programStartSymbol;
                }
            }
            Module compiledMod = null;
            if (options.module == null) {
                options.module = def.mainSyntaxModuleName();
                switch (options.input) {
                case KORE:
                    compiledMod = def.languageParsingModule();
                    break;
                default:
                    compiledMod = def.kompiledDefinition.getModule(def.mainSyntaxModuleName()).get();
                }
            }
            Option<Module> maybeMod = def.programParsingModuleFor(options.module, kem);
            if (maybeMod.isEmpty()) {
                throw KEMException.innerParserError("Module " + options.module + " not found. Specify a module with -m.");
            }
            Module mod = maybeMod.get();

            K parsed = kread.prettyRead(mod, sort, def, source, FileUtil.read(stringToParse), options.input);

            if (options.expandMacros || options.kore) {
                parsed = ExpandMacros.forNonSentences(compiledMod, files.get(), def.kompileOptions, false).expand(parsed);
            }

            if (options.kore) {
              ModuleToKORE converter = new ModuleToKORE(compiledMod, files.get(), def.topCellInitializer, def.kompileOptions);
              parsed = new AddSortInjections(compiledMod).addSortInjections(parsed, sort);
              converter.convert(parsed);
              System.out.println(converter.toString());
            } else {
              System.out.println(new String(kprint.prettyPrint(def, compiledMod, parsed), StandardCharsets.UTF_8));
            }
            sw.printTotal("Total");
            return 0;
        } finally {
            scope.exit();
        }
    }
}

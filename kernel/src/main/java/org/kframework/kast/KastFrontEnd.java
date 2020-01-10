// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kast;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.attributes.Source;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.main.FrontEnd;
import org.kframework.parser.KRead;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.parser.concrete2kore.kernel.Scanner;
import org.kframework.parser.concrete2kore.kernel.KSyntax2Bison;
import org.kframework.parser.outer.Outer;
import org.kframework.unparser.KPrint;
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
import org.kframework.utils.Stopwatch;
import scala.Option;

import java.io.File;
import java.io.IOException;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
    private final Provider<KPrint> kprint;
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
            Provider<FileUtil> files,
            @KompiledDir Provider<File> kompiledDir,
            Provider<CompiledDefinition> compiledDef,
            Provider<KPrint> kprint,
            DefinitionScope scope) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.sw = sw;
        this.kem = kem;
        this.files = files;
        this.env = env;
        this.kompiledDir = kompiledDir;
        this.compiledDef = compiledDef;
        this.kprint = kprint;
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
            Reader stringToParse = null;
            File outputFile = null;
            if (!options.genParser) {
              stringToParse = options.stringToParse();
            } else {
              outputFile = options.outputFile();
            }
            Source source = options.source();

            CompiledDefinition def = compiledDef.get();
            KRead kread = new KRead(kem, files.get(), options.input);

            org.kframework.kore.Sort sort = options.sort;
            if (sort == null) {
                if (env.get("KRUN_SORT") != null) {
                    sort = Outer.parseSort(env.get("KRUN_SORT"));
                } else {
                    sort = def.programStartSymbol;
                }
            }
            Module unparsingMod;
            if (options.module == null) {
                options.module = def.mainSyntaxModuleName();
                switch (options.input) {
                    case KORE:
                        unparsingMod = def.languageParsingModule();
                        break;
                    default:
                        unparsingMod = def.kompiledDefinition.getModule(def.mainSyntaxModuleName()).get();
                }
            } else {
                Option<Module> maybeUnparsingMod = def.kompiledDefinition.getModule(options.module);
                if (maybeUnparsingMod.isEmpty()) {
                    throw KEMException.innerParserError("Module " + options.module + " not found.");
                }
                unparsingMod = maybeUnparsingMod.get();
            }
            Option<Module> maybeMod = def.programParsingModuleFor(options.module, kem);
            if (maybeMod.isEmpty()) {
                throw KEMException.innerParserError("Module " + options.module + " not found. Specify a module with -m.");
            }
            Module parsingMod = maybeMod.get();

            if (options.genParser) {
              kread.createBisonParser(parsingMod, sort, outputFile);
            } else {
              K parsed = kread.prettyRead(parsingMod, sort, def, source, FileUtil.read(stringToParse));

              if (options.expandMacros) {
                  parsed = ExpandMacros.forNonSentences(unparsingMod, files.get(), def.kompileOptions, false).expand(parsed);
              }

              System.out.print(new String(kprint.get().prettyPrint(def, unparsingMod, parsed), StandardCharsets.UTF_8));
            }
            sw.printTotal("Total");
            return 0;
        } finally {
            scope.exit();
        }
    }
}

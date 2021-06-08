// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kast;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
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
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.Stopwatch;
import scala.Option;

import java.io.File;
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
    private final Provider<Definition> kompiledDefinition;
    private final Provider<KPrint> kprint;
    private final DefinitionScope scope;

    @Inject
    KastFrontEnd(
            KastOptions options,
            @Usage String usage,
            Stopwatch sw,
            KExceptionManager kem,
            JarInfo jarInfo,
            @Environment Map<String, String> env,
            Provider<FileUtil> files,
            @KompiledDir Provider<File> kompiledDir,
            Provider<Definition> kompiledDefinition,
            Provider<KPrint> kprint,
            DefinitionScope scope) {
        super(kem, options.global, usage, jarInfo, files);
        this.options = options;
        this.sw = sw;
        this.kem = kem;
        this.files = files;
        this.env = env;
        this.kompiledDir = kompiledDir;
        this.kompiledDefinition = kompiledDefinition;
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
            org.kframework.kore.Sort sort = options.sort;
            Definition kompiledDefinition = this.kompiledDefinition.get();
            if (sort == null) {
                if (env.get("KRUN_SORT") != null) {
                    sort = Outer.parseSort(env.get("KRUN_SORT"));
                } else {
                    sort = Outer.parseSort(kompiledDefinition.att().get("startSymbol"));
                }
            }

            Module unparsingMod;
            if (options.module == null) {
                options.module = kompiledDefinition.att().get(Att.SYNTAX_MODULE());
                switch (options.input) {
                    case KORE:
                        unparsingMod = kompiledDefinition.getModule("LANGUAGE-PARSING").get();
                        break;
                    default:
                        unparsingMod = kompiledDefinition.getModule(options.module).get();
                }
            } else {
                Option<Module> maybeUnparsingMod = kompiledDefinition.getModule(options.module);
                if (maybeUnparsingMod.isEmpty()) {
                    throw KEMException.innerParserError("Module " + options.module + " not found.");
                }
                unparsingMod = maybeUnparsingMod.get();
            }

            Option<Module> maybeMod = CompiledDefinition.programParsingModuleFor(kompiledDefinition, options.module, kem);
            if (maybeMod.isEmpty()) {
                throw KEMException.innerParserError("Module " + options.module + " not found. Specify a module with -m.");
            }
            Module parsingMod = maybeMod.get();

            KRead kread = new KRead(kem, files.get(), options.input);
            if (options.genParser || options.genGlrParser) {
                kread.createBisonParser(parsingMod, sort, options.bisonOutputFile(), options.genGlrParser, options.bisonFile, options.bisonStackMaxDepth);
            } else {
                Reader stringToParse = options.stringToParse();
                Source source = options.source();
                K parsed = kread.prettyRead(parsingMod, sort, source, FileUtil.read(stringToParse));

                if (sort.equals(Sorts.K())) {
                    sort = Sorts.KItem();
                }

                kprint.get().prettyPrint(kompiledDefinition, unparsingMod, s -> kprint.get().outputFile(s), parsed, sort);
            }

            sw.printTotal("Total");
            return 0;
        } finally {
            scope.exit();
        }
    }
}

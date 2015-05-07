// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kast;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.attributes.Source;
import org.kframework.backend.unparser.KoreFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.ToKast;
import org.kframework.main.FrontEnd;
import org.kframework.parser.ProgramLoader;
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
import org.kframework.utils.inject.Main;
import scala.Option;

import java.io.File;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.kframework.kore.KORE.*;

public class KastFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KastModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }

    private final KastOptions options;
    private final Provider<Context> contextProvider;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final Map<String, String> env;
    private final Provider<ProgramLoader> loader;
    private final Provider<File> kompiledDir;
    private final Provider<CompiledDefinition> compiledDef;
    private final DefinitionScope scope;

    @Inject
    KastFrontEnd(
            KastOptions options,
            @Main Provider<Context> contextProvider,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Stopwatch sw,
            KExceptionManager kem,
            JarInfo jarInfo,
            @Environment Map<String, String> env,
            Provider<ProgramLoader> loader,
            FileUtil files,
            @KompiledDir Provider<File> kompiledDir,
            Provider<CompiledDefinition> compiledDef,
            DefinitionScope scope) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.contextProvider = contextProvider;
        this.sw = sw;
        this.kem = kem;
        this.env = env;
        this.loader = loader;
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

            if (options.experimental.kore) {
                CompiledDefinition def = compiledDef.get();
                org.kframework.kore.Sort sort = options.sort;
                if (sort == null) {
                    if (env.get("KRUN_SORT") != null) {
                        sort = Sort(env.get("KRUN_SORT"));
                    } else {
                        sort = def.programStartSymbol;
                    }
                }
                org.kframework.definition.Module mod;
                if (options.module == null) {
                    mod = def.getParsedDefinition().mainSyntaxModule();
                } else {
                    Option<org.kframework.definition.Module> mod2 = def.getParsedDefinition().getModule(options.module);
                    if (mod2.isEmpty()) {
                        throw KEMException.innerParserError("Module " + options.module + " not found. Specify a module with -m.");
                    }
                    mod = mod2.get();
                }
                K parsed = def.getParser(mod, sort, kem).apply(FileUtil.read(stringToParse), source);
                System.out.println(ToKast.apply(parsed));
            } else {
                Context context = contextProvider.get();
                Sort sort = sort(options.sort, context);

                ASTNode out = loader.get().processPgm(stringToParse, source, sort, context, options.parser);
                StringBuilder kast;
                KoreFilter koreFilter = new KoreFilter(context);
                StringBuilder sb = new StringBuilder();
                koreFilter.visitNode(out, sb);
                kast = sb;
                kast.append("\n");

                System.out.print(kast.toString());
            }
            sw.printTotal("Total");
            return 0;
        } finally {
            scope.exit();
        }
    }


    private Sort sort(org.kframework.kore.Sort sort, Context context) {
        Sort res;
        if (sort == null) {
            if (env.get("KRUN_SORT") != null) {
                res = Sort.of(env.get("KRUN_SORT"));
            } else {
                res = context.startSymbolPgm();
            }
        } else {
            res = Sort.of(sort.name());
        }
        return res;
    }
}

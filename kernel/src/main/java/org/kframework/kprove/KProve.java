// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kprove;

import com.google.inject.Inject;
import org.apache.commons.io.FilenameUtils;
import org.kframework.compile.*;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Option;
import scala.Tuple2;

import java.io.File;
import java.util.*;
import java.util.function.Function;


/**
 * Class that implements the "--prove" option.
 */
public class KProve {

    private final KExceptionManager kem;
    private final Stopwatch sw;
    private final FileUtil files;
    private static KPrint kprint;
    private static Tuple2<Definition, Module> compiled;
    private static CompiledDefinition compiledDefinition;


    @Inject
    public KProve(KExceptionManager kem, Stopwatch sw, FileUtil files, KPrint kprint) {
        this.kem    = kem;
        this.sw     = sw;
        this.files  = files;
        this.kprint = kprint;
    }

    public int run(KProveOptions options, CompiledDefinition compiledDefinition, Backend backend, Function<Module, Rewriter> rewriterGenerator) {
        compiled = getProofDefinition(options.specFile(files), options.defModule, options.specModule, compiledDefinition, backend, files, kem, sw);
        KProve.compiledDefinition = compiledDefinition;
        Rewriter rewriter = rewriterGenerator.apply(compiled._1().mainModule());
        Module specModule = compiled._2();

        options.global.logStmtsOnly |= options.global.log;
        options.global.logBasic |= options.global.logStmtsOnly;
        options.global.verbose |= options.global.logBasic;
        options.global.debug |= options.global.debugFull;
        K results = rewriter.prove(specModule);
        int exit;
        if (results instanceof KApply) {
            KApply kapp = (KApply) results;
            exit = kapp.klabel().name().equals("#True") ? 0 : 1;
        } else {
            exit = 1;
        }
        //kprint.prettyPrint(compiled._1(), compiled._1().getModule("LANGUAGE-PARSING").get(), s -> kprint.outputFile(s), results);
        return exit;
    }

    public static void prettyPrint(K results) {
        Option<Module> module = compiled._1().getModule("LANGUAGE-PARSING");
        kprint.prettyPrint(
                compiled._1(),
                module.get(),
                s -> kprint.outputFile(s),
                results);
    }

    private static Module getModule(String defModule, Map<String, Module> modules, Definition oldDef) {
        if (modules.containsKey(defModule))
            return modules.get(defModule);
        Option<Module> mod = oldDef.getModule(defModule);
        if (mod.isDefined()) {
            return mod.get();
        }
        throw KEMException.criticalError("Module " + defModule + " does not exist.");
    }

    public static Map<Definition, Definition> cache = Collections.synchronizedMap(new LinkedHashMap<Definition, Definition>() {
        @Override
        protected boolean removeEldestEntry(Map.Entry entry) {
            return size() > 10;
        }
    });

    public static Tuple2<Definition, Module> getProofDefinition(File proofFile, String defModuleName, String specModuleName, CompiledDefinition compiledDefinition, Backend backend, FileUtil files, KExceptionManager kem, Stopwatch sw) {
        Kompile kompile = new Kompile(compiledDefinition.kompileOptions, files, kem, sw, true);
        if (defModuleName == null) {
            defModuleName = compiledDefinition.kompiledDefinition.mainModule().name();
        }
        if (specModuleName == null) {
            specModuleName = FilenameUtils.getBaseName(proofFile.getName()).toUpperCase();
        }
        java.util.Set<Module> modules = kompile.parseModules(compiledDefinition, defModuleName, files.resolveWorkingDirectory(proofFile).getAbsoluteFile());
        Map<String, Module> modulesMap = new HashMap<>();
        modules.forEach(m -> modulesMap.put(m.name(), m));
        Module defModule = getModule(defModuleName, modulesMap, compiledDefinition.getParsedDefinition());
        Module specModule = getModule(specModuleName, modulesMap, compiledDefinition.getParsedDefinition());
        specModule = backend.specificationSteps(compiledDefinition.kompiledDefinition).apply(specModule);
        specModule = spliceModule(specModule, compiledDefinition.kompiledDefinition);
        Definition combinedDef = Definition.apply(defModule, compiledDefinition.getParsedDefinition().entryModules(), compiledDefinition.getParsedDefinition().att());
        Definition compiled = compileDefinition(backend, combinedDef);
        return Tuple2.apply(compiled, specModule);
    }

    private static Definition compileDefinition(Backend backend, Definition combinedDef) {
        Definition compiled = cache.get(combinedDef);
        if (compiled == null) {
            compiled = backend.steps().apply(combinedDef);
            cache.put(combinedDef, compiled);
        }
        return compiled;
    }

    private static Module spliceModule(Module specModule, Definition kompiledDefinition) {
        return ModuleTransformer.from(mod -> kompiledDefinition.getModule(mod.name()).isDefined() ? kompiledDefinition.getModule(mod.name()).get() : mod, "splice imports of specification module").apply(specModule);
    }
}

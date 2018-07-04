// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.kprove;

import com.google.inject.Inject;
import org.apache.commons.io.FilenameUtils;
import org.kframework.Debugg;
import org.kframework.attributes.Att;
import org.kframework.compile.*;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.krun.KRun;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import org.kframework.unparser.KPrint;
import scala.Option;
import scala.Tuple2;
import scala.collection.Set;

import java.io.File;
import java.util.*;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;


/**
 * Class that implements the "--prove" option.
 */
public class KProve {

    private final KExceptionManager kem;
    private final Stopwatch sw;
    private final FileUtil files;
    private TTYInfo tty;
    private KPrint kprint;

    @Inject
    public KProve(KExceptionManager kem, Stopwatch sw, FileUtil files, TTYInfo tty, KPrint kprint) {
        this.kem = kem;
        this.sw = sw;
        this.files = files;
        this.tty = tty;
        this.kprint = kprint;
    }

    public int run(KProveOptions options, CompiledDefinition compiledDefinition, Backend backend, Function<Module, Rewriter> rewriterGenerator) {
        Tuple2<Definition, Module> compiled = getProofDefinition(options.specFile(files), options.defModule, options.specModule, compiledDefinition, backend, options.global, files, kem, sw);
        Rewriter rewriter = rewriterGenerator.apply(compiled._1().mainModule());
        Module specModule = compiled._2();
        Debugg.init(options, files, specModule, compiled._1().getModule("LANGUAGE-PARSING").get(), kprint);
        Debugg.log("spec " + options.specFile(files).getAbsolutePath());
        K results;
        try {
            results = rewriter.prove(specModule);
        } catch (AssertionError e) {
            Debugg.log(Debugg.LogEvent.CRASH);
            Debugg.close();
            throw e;
        }
        int exit;
        if (results instanceof KApply) {
            KApply kapp = (KApply) results;
            exit = kapp.klabel().name().equals("#True") ? 0 : 1;
        } else {
            exit = 1;
        }
        kprint.prettyPrint(compiled._1().getModule("LANGUAGE-PARSING").get(), s -> kprint.outputFile(s), results);
        Debugg.close();
        return exit;
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

    public static Tuple2<Definition, Module> getProofDefinition(File proofFile, String defModuleName, String specModuleName, CompiledDefinition compiledDefinition, Backend backend, GlobalOptions options, FileUtil files, KExceptionManager kem, Stopwatch sw) {
        Kompile kompile = new Kompile(compiledDefinition.kompileOptions, options, files, kem, sw, true);
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
        Definition combinedDef = Definition.apply(defModule, compiledDefinition.getParsedDefinition().entryModules(), Att.empty());
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

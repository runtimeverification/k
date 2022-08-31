package org.kframework.kprovex;

import com.google.common.collect.Sets;
import com.google.inject.Inject;
import org.apache.commons.io.FilenameUtils;
import org.kframework.attributes.Att;
import org.kframework.compile.Backend;
import org.kframework.definition.Module;
import org.kframework.definition.*;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kprove.KProveOptions;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import scala.Option;
import scala.Tuple2;

import java.io.File;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;

public class ProofDefinitionBuilder {

    private final CompiledDefinition compiledDefinition;
    private final Backend backend;
    private final Kompile kompile;
    private final KProveOptions proveOptions;
    private final FileUtil files;
    private final Stopwatch sw;

    @Inject
    public ProofDefinitionBuilder(CompiledDefinition compiledDefinition, Backend backend, Kompile kompile,
                                  KProveOptions proveOptions, FileUtil files, Stopwatch sw) {
        this.compiledDefinition = compiledDefinition;
        this.backend = backend;
        this.kompile = kompile;
        this.proveOptions = proveOptions;
        this.files = files;
        this.sw = sw;
    }

    /**
     * @param specFile       File containing specification rules to prove. Not part of definition.
     * @param specModuleName Module containing specifications to prove
     */
    public Tuple2<Definition, Module> build(File specFile, String specModuleName, boolean readOnlyCache) {
        String defModuleNameUpdated = compiledDefinition.kompiledDefinition.mainModule().name();
        String specModuleNameUpdated =
                specModuleName == null ? FilenameUtils.getBaseName(specFile.getName()).toUpperCase() : specModuleName;
        File absSpecFile = files.resolveWorkingDirectory(specFile).getAbsoluteFile();

        Set<Module> modules = kompile.parseModules(compiledDefinition, defModuleNameUpdated, specModuleNameUpdated, absSpecFile,
                backend.excludedModuleTags(), true, true);
        Map<String, Module> modulesMap = modules.stream().collect(Collectors.toMap(Module::name, m -> m));
        Definition parsedDefinition = compiledDefinition.getParsedDefinition();
        Module specModule = getModule(specModuleNameUpdated, modulesMap, parsedDefinition);
        specModule = filter(specModule);
        kompile.proverChecksX(specModule, modulesMap.get(defModuleNameUpdated));
        kompile.structuralChecks(immutable(modules), specModule, Option.empty(), backend.excludedModuleTags());
        specModule = backend.specificationSteps(compiledDefinition.kompiledDefinition).apply(specModule);
        sw.printIntermediate("Apply prover steps");
        return Tuple2.apply(compiledDefinition.kompiledDefinition, specModule);
    }

    private static Module getModule(String defModule, Map<String, Module> modules, Definition parsedDefinition) {
        if (modules.containsKey(defModule))
            return modules.get(defModule);
        Option<Module> mod = parsedDefinition.getModule(defModule);
        if (mod.isDefined()) {
            return mod.get();
        }
        throw KEMException.criticalError("Module " + defModule + " does not exist.");
    }

    // filter claims according the command line options
    private Module filter(Module specModule) {
        if (proveOptions.trusted != null || proveOptions.exclude != null || proveOptions.claims != null) {
            Set<String> unused = new HashSet<>();
            if (proveOptions.trusted != null) unused.addAll(proveOptions.trusted);
            if (proveOptions.exclude != null) unused.addAll(proveOptions.exclude);
            if (proveOptions.claims != null) unused.addAll(proveOptions.claims);
            if (proveOptions.exclude != null && proveOptions.claims != null) {
                Sets.SetView<String> intersection = Sets.intersection(new HashSet<>(proveOptions.exclude), new HashSet<>(proveOptions.claims));
                if (intersection.size() != 0)
                    throw KEMException.criticalError("Labels used for both --exclude and --claims: " + intersection);
            }
            specModule = new ModuleTransformer((m -> {
                Set<Sentence> filtered = stream(m.localSentences()).flatMap(s -> {
                    if (s instanceof Claim && s.att().getOptional("label").isPresent()) {
                        String label = s.att().getOptional("label").get();
                        Claim c = (Claim) s;
                        if (proveOptions.trusted != null && proveOptions.trusted.contains(label)) {
                            s = c.newInstance(c.body(), c.requires(), c.ensures(), c.att().add(Att.TRUSTED()));
                            unused.remove(label);
                        }
                        if (proveOptions.exclude != null && proveOptions.exclude.contains(label)) {
                            unused.remove(label);
                            return Stream.empty();
                        }
                        if (proveOptions.claims != null)
                            if (proveOptions.claims.contains(label))
                                unused.remove(label);
                            else
                                return Stream.empty();
                    }
                    return Stream.of(s);
                }).collect(Collectors.toSet());
                return Module.apply(m.name(), m.imports(), immutable(filtered), m.att());
            }), "Filter claims") {
            }.apply(specModule);
            if (unused.size() != 0)
                throw KEMException.criticalError("Unused filtering labels: " + unused);
        }
        return specModule;
    }
}

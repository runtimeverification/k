// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser;

import com.google.common.collect.Streams;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.tuple.Triple;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.FlatModule;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Require;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.Kompile;
import org.kframework.kore.convertors.KILtoKORE;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.inner.ApplySynonyms;
import org.kframework.parser.inner.CollectProductionsVisitor;
import org.kframework.parser.outer.ExtractFencedKCodeFromMarkdown;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.OuterParsingOptions;

import java.io.File;
import java.io.IOException;
import java.nio.file.LinkOption;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * A few functions that are a common pattern when calling the new parser.
 */
public class ParserUtils {

    private final KExceptionManager kem;
    private final GlobalOptions options;
    private final FileUtil files;
    private final ExtractFencedKCodeFromMarkdown mdExtractor;

    public ParserUtils(FileUtil files, KExceptionManager kem) {
        this(files, kem, new GlobalOptions(), new OuterParsingOptions());
    }

    public ParserUtils(FileUtil files, KExceptionManager kem, GlobalOptions options, OuterParsingOptions outerParsingOptions) {
        this.kem = kem;
        this.options = options;
        this.files = files;
        mdExtractor = new ExtractFencedKCodeFromMarkdown(this.kem, outerParsingOptions.mdSelector);
    }

    /**
     * Takes a definition in e-kore textual format and a main module name, and returns the KORE
     * representation of that module. Current implementation uses JavaCC and goes through KIL.
     *
     * @param definitionText textual representation of the modules.
     * @param mainModule     main module name.
     * @return KORE representation of the main module.
     */
    public static Module parseMainModuleOuterSyntax(String definitionText, Source source, String mainModule) {
        Definition def = new Definition();
        def.setItems(Outer.parse(source, definitionText, null));
        def.setMainModule(mainModule);
        def.setMainSyntaxModule(mainModule);

        Context context = new Context();
        new CollectProductionsVisitor(false, context).visit(def);

        KILtoKORE kilToKore = new KILtoKORE(context);
        return kilToKore.apply(def).getModule(mainModule).get();
    }

    public List<org.kframework.kil.Module> slurp(
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories,
            Set<File> requiredFiles) {
        try {
            source = Source.apply(Paths.get(source.source()).toRealPath(LinkOption.NOFOLLOW_LINKS).toString());
        } catch (IOException e) {
            // if it fails, just keep the original option
        }
        if (source.source().endsWith(".md")) {
            definitionText = mdExtractor.extract(definitionText, source);
            if (options.debug()) { // save .k files in temp directory
                String fname = new File(source.source()).getName();
                fname = fname.substring(0, fname.lastIndexOf(".md")) + ".k";
                File file = files.resolveTemp(".md2.k/" + fname);
                // if multiple files exists with the same name, append an index
                // and add a comment at the end of the file with the full path
                // Note: the comment is not sent to the parser
                int index = 2;
                while (file.exists())
                    file = files.resolveTemp(".md2.k/" + fname + "_" + index++);
                FileUtil.save(file, definitionText + "\n// " + source.source() + "\n");
            }
        }
        List<DefinitionItem> items = Outer.parse(source, definitionText, null);
        if (options.verbose) {
            System.out.println("Importing: " + source);
        }
        List<org.kframework.kil.Module> results = new ArrayList<>();

        for (DefinitionItem di : items) {
            if (di instanceof org.kframework.kil.Module)
                results.add((org.kframework.kil.Module) di);
            else if (di instanceof Require) {
                // resolve location of the new file

                String definitionFileName = ((Require) di).getValue();

                if (definitionFileName.equals("ffi.k") || definitionFileName.equals("json.k") ||
                    definitionFileName.equals("rat.k") || definitionFileName.equals("substitution.k") ||
                    definitionFileName.equals("domains.k") || definitionFileName.equals("kast.k")) {
                    kem.registerCompilerWarning(ExceptionType.FUTURE_ERROR,
                        "Requiring a K file in the K builtin directory via " +
                        "a deprecated filename. Please replace \"" + definitionFileName +
                        "\" with \"" + definitionFileName.substring(0, definitionFileName.length() - 2) + ".md\".", di);
                    definitionFileName = definitionFileName.substring(0, definitionFileName.length() - 2) + ".md";
                }

                String finalDefinitionFile = definitionFileName;

                ArrayList<File> allLookupDirectories = new ArrayList<>(lookupDirectories);
                allLookupDirectories.add(1, currentDirectory); //after builtin directory but before anything else

                Optional<File> definitionFile = allLookupDirectories.stream()
                        .map(lookupDirectory -> {
                            if (new File(finalDefinitionFile).isAbsolute()) {
                                return new File(finalDefinitionFile);
                            } else {
                                return new File(lookupDirectory, finalDefinitionFile);
                            }
                        })
                        .filter(file -> file.exists()).findFirst();

                if (definitionFile.isPresent()) {
                    File canonical = definitionFile.get().getAbsoluteFile();
                    try {
                        canonical = definitionFile.get().toPath().toRealPath(LinkOption.NOFOLLOW_LINKS).toFile();
                    } catch (IOException e) {
                        // if it fails, just keep the original option
                    }
                    if (!requiredFiles.contains(canonical)) {
                        requiredFiles.add(canonical);
                        results.addAll(slurp(loadDefinitionText(canonical),
                                Source.apply(canonical.getAbsolutePath()),
                                canonical.getParentFile(),
                                lookupDirectories, requiredFiles));
                    }
                } else {
                    throw KEMException.criticalError("Could not find file: " +
                            finalDefinitionFile + "\nLookup directories:" + allLookupDirectories, di);
                }
            }
        }
        return results;
    }

    private String loadDefinitionText(File definitionFile) {
        try {
            return FileUtils.readFileToString(files.resolveWorkingDirectory(definitionFile));
        } catch (IOException e) {
            throw KEMException.criticalError(e.getMessage(), e);
        }
    }

    public Set<Module> loadModules(
            Set<Module> previousModules,
            Context context,
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories,
            Set<File> requiredFiles,
            boolean kore,
            boolean preprocess,
            boolean leftAssoc) {

        List<org.kframework.kil.Module> kilModules =
                slurp(definitionText, source, currentDirectory, lookupDirectories, requiredFiles);

        Definition def = new Definition();
        def.setItems((List<DefinitionItem>) (Object) kilModules);

        new CollectProductionsVisitor(kore, context).visit(def);

        // Triple of moduleName, Source, Location
        Map<String, List<Triple<String, Source, Location>>> groupedModules =
                Streams.concat(
                        previousModules.stream().map(m -> Triple.of(m.name(), m.att().get(Att.SOURCE(), Source.class),
                                m.att().get(Att.LOCATION(), Location.class))),
                        kilModules.stream().map(m -> Triple.of(m.getName(), m.getSource(), m.getLocation())))
                // make sure we have unique modules (double requires), and preserve order
                .collect(Collectors.toCollection(LinkedHashSet::new)).stream()
                .collect(Collectors.groupingBy(Triple::getLeft));

        List<String> duplicateModules = groupedModules
          .entrySet().stream()
          .filter(e -> e.getValue().size() > 1)
          .map(Map.Entry::getKey)
          .collect(Collectors.toList());

        int errors = 0;
        for (String moduleName : duplicateModules) {
          Triple<String, Source, Location> firstMod = groupedModules.get(moduleName).get(0);
          Triple<String, Source, Location> secondMod = groupedModules.get(moduleName).get(1);
          KEMException ex = KEMException.outerParserError("Module " + moduleName + " previously declared at "
                  + firstMod.getMiddle() + " and " + firstMod.getRight(), secondMod.getMiddle(), secondMod.getRight());
          errors++;
          kem.addKException(ex.getKException());
        }

        if (errors > 0) {
          throw KEMException.outerParserError("Had " + errors + " outer parsing errors.");
        }

        if (preprocess) {
          System.out.println(def.toString());
        }

        KILtoKORE kilToKore = new KILtoKORE(context, false, kore, leftAssoc);
        // Order modules by name to stabilize the error message for circular imports
        java.util.List<FlatModule> flatModules = kilModules.stream().map(kilToKore::toFlatModule).sorted(Comparator.comparing(FlatModule::name)).collect(Collectors.toList());
        Set<Module> finalModules = mutable(FlatModule.toModules(immutable(flatModules), immutable(previousModules)));

        Set<Module> result = new HashSet<>();
        ModuleTransformer applySynonyms = ModuleTransformer.fromSentenceTransformer(new ApplySynonyms()::apply, "Apply sort synonyms");
        for (Module mod : finalModules) {
            result.add(applySynonyms.apply(mod));
        }
        return result;
    }

    public org.kframework.definition.Definition loadDefinition(
            String mainModuleName,
            Set<Module> previousModules,
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories,
            boolean kore,
            boolean preprocess,
            boolean leftAssoc) {
        Set<Module> modules = loadModules(previousModules, new Context(), definitionText, source, currentDirectory, lookupDirectories, new HashSet<>(), kore, preprocess, leftAssoc);
        Set<Module> allModules = new HashSet<>(modules);
        allModules.addAll(previousModules);
        Module mainModule = getMainModule(mainModuleName, allModules);
        return org.kframework.definition.Definition.apply(mainModule, immutable(allModules), Att.empty());
    }

    public org.kframework.definition.Definition loadDefinition(
            String mainModuleName,
            String syntaxModuleName,
            String definitionText,
            File source,
            File currentDirectory,
            List<File> lookupDirectories,
            boolean autoImportDomains,
            boolean kore,
            boolean preprocess,
            boolean leftAssoc) {
        String strSource = source.getAbsolutePath();
        try {
            strSource = source.toPath().toRealPath(LinkOption.NOFOLLOW_LINKS).toString();
        } catch (IOException e) {
            // if it fails, just keep the original option
        }
        return loadDefinition(mainModuleName, syntaxModuleName, definitionText,
                Source.apply(strSource),
                currentDirectory, lookupDirectories, autoImportDomains, kore, preprocess, leftAssoc);
    }

    public org.kframework.definition.Definition loadDefinition(
            String mainModuleName,
            String syntaxModuleName,
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories,
            boolean autoImportDomains,
            boolean kore,
            boolean preprocess,
            boolean leftAssoc) {
        Set<Module> previousModules = new HashSet<>();
        Set<File> requiredFiles = new HashSet<>();
        Context context = new Context();
        if (autoImportDomains)
            previousModules.addAll(loadModules(new HashSet<>(), context, Kompile.REQUIRE_PRELUDE_K, Source.apply("Auto imported prelude"), currentDirectory, lookupDirectories, requiredFiles, kore, preprocess, leftAssoc));
        Set<Module> modules = loadModules(previousModules, context, definitionText, source, currentDirectory, lookupDirectories, requiredFiles, kore, preprocess, leftAssoc);
        if (preprocess) {
          System.exit(0);
        }
        modules.addAll(previousModules); // add the previous modules, since load modules is not additive
        Module mainModule = getMainModule(mainModuleName, modules);
        Optional<Module> opt;
        opt = modules.stream().filter(m -> m.name().equals(syntaxModuleName)).findFirst();
        Module syntaxModule;
        if (!opt.isPresent()) {
            kem.registerCompilerWarning(ExceptionType.MISSING_SYNTAX_MODULE, "Could not find main syntax module with name " + syntaxModuleName
                    + " in definition.  Use --syntax-module to specify one. Using " + mainModuleName + " as default.");
            syntaxModule = mainModule;
        } else {
            syntaxModule = opt.get();
        }

        return org.kframework.definition.Definition.apply(mainModule, immutable(modules), Att().add(Att.SYNTAX_MODULE(), syntaxModule.name()));
    }

    private Module getMainModule(String mainModuleName, Set<Module> modules) {
        Optional<Module> opt = modules.stream().filter(m -> m.name().equals(mainModuleName)).findFirst();
        if (!opt.isPresent()) {
            throw KEMException.compilerError("Could not find main module with name " + mainModuleName
                    + " in definition. Use --main-module to specify one.");
        }
        return opt.get();
    }
}

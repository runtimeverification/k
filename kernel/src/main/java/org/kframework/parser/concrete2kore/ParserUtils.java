// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.apache.commons.io.FileUtils;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Require;
import org.kframework.kil.loader.CollectProductionsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kore.K;
import org.kframework.kore.convertors.KILtoKORE;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

/**
 * A few functions that are a common pattern when calling the new parser.
 */
public class ParserUtils {

    private final FileUtil files;

    public ParserUtils(FileUtil files) {
        this.files = files;
    }
    public static K parseWithFile(CharSequence theTextToParse,
                                  String mainModule,
                                  String startSymbol,
                                  File definitionFile) {
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return parseWithString(theTextToParse, mainModule, startSymbol, Source.apply(definitionFile.getAbsolutePath()), definitionText);
    }

    public static K parseWithString(CharSequence theTextToParse,
                                    String mainModule,
                                    String startSymbol,
                                    Source source,
                                    String definitionText) {
        Module kastModule = parseMainModuleOuterSyntax(definitionText, source, mainModule);
        return parseWithModule(theTextToParse, startSymbol, source, kastModule);
    }

    public static K parseWithModule(CharSequence theTextToParse,
                                    String startSymbol,
                                    Source source,
                                    org.kframework.definition.Module kastModule) {
        ParseInModule parser = new ParseInModule(kastModule);
        return parseWithModule(theTextToParse, startSymbol, source, parser);
    }

    public static K parseWithModule(CharSequence theTextToParse,
                                    String startSymbol,
                                    Source source,
                                    ParseInModule kastModule) {
        Term cleaned = kastModule.parseString(theTextToParse, startSymbol, source)._1().right().get();
        return TreeNodesToKORE.apply(cleaned);
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
        new CollectProductionsVisitor(context).visitNode(def);

        KILtoKORE kilToKore = new KILtoKORE(context);
        return kilToKore.apply(def).getModule(mainModule).get();
    }

    private List<org.kframework.kil.Module> slurp(
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories) {
        List<DefinitionItem> items = Outer.parse(source, definitionText, null);

        List<org.kframework.kil.Module> results = new ArrayList<>();

        for (DefinitionItem di : items) {
            if (di instanceof org.kframework.kil.Module)
                results.add((org.kframework.kil.Module) di);
            else if (di instanceof Require) {
                // resolve location of the new file

                String definitionFileName = ((Require) di).getValue();

                ArrayList<File> allLookupDirectoris = new ArrayList<>(lookupDirectories);
                allLookupDirectoris.add(0, currentDirectory);

                Optional<File> definitionFile = allLookupDirectoris.stream()
                        .map(lookupDirectory -> new File(lookupDirectory.getAbsolutePath() + "/" + definitionFileName))
                        .filter(file -> file.exists()).findFirst();

                if (definitionFile.isPresent())
                    results.addAll(slurp(files.loadFromWorkingDirectory(definitionFile.get().getPath()),
                            Source.apply(definitionFile.get().getAbsolutePath()),
                            definitionFile.get().getParentFile(),
                            lookupDirectories));
                else
                    throw KExceptionManager.criticalError("Could not find file: " +
                            definitionFileName + "\nLookup directories:" + allLookupDirectoris, di);
            }
        }
        return results;
    }

    public Set<Module> loadModules(
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories) {

        List<org.kframework.kil.Module> kilModules =
                slurp(definitionText, source, currentDirectory, lookupDirectories);

        Definition def = new Definition();
        def.setItems((List<DefinitionItem>) (Object) kilModules);

        Context context = new Context();
        new CollectProductionsVisitor(context).visitNode(def);

        KILtoKORE kilToKore = new KILtoKORE(context, false, false);

        HashMap<String, Module> koreModules = new HashMap<>();
        HashSet<org.kframework.kil.Module> kilModulesSet = new HashSet<>(kilModules);

        kilModules.stream().forEach(m -> kilToKore.apply(m, kilModulesSet, koreModules));

        return new HashSet<>(koreModules.values());
    }

    public org.kframework.definition.Definition loadDefinition(
            String mainModuleName,
            String syntaxModuleName,
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories) {
        Set<Module> modules = loadModules(definitionText, source, currentDirectory, lookupDirectories);
        Module mainModule = modules.stream().filter(m -> m.name().equals(mainModuleName)).findFirst().get();
        Module syntaxModule = modules.stream().filter(m -> m.name().equals(syntaxModuleName)).findFirst().get();
        return org.kframework.definition.Definition.apply(mainModule, syntaxModule, immutable(modules), Att());
    }
}

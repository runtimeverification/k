// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.apache.commons.io.FileUtils;
import org.kframework.definition.Module;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Require;
import org.kframework.kil.Source;
import org.kframework.kil.Sources;
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
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

/**
 * A few functions that are a common pattern when calling the new parser.
 */
public class ParserUtils {

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
        return parseWithString(theTextToParse, mainModule, startSymbol, definitionText);
    }

    public static K parseWithString(CharSequence theTextToParse,
                                    String mainModule,
                                    String startSymbol,
                                    String definitionText) {
        Module kastModule = parseMainModuleOuterSyntax(definitionText, mainModule);
        return parseWithModule(theTextToParse, startSymbol, kastModule);
    }

    public static K parseWithModule(CharSequence theTextToParse,
                                    String startSymbol,
                                    org.kframework.definition.Module kastModule) {
        ParseInModule parser = new ParseInModule(kastModule);
        return parseWithModule(theTextToParse, startSymbol, parser);
    }

    public static K parseWithModule(CharSequence theTextToParse,
                                    String startSymbol,
                                    ParseInModule kastModule) {
        Term cleaned = kastModule.parseString(theTextToParse, startSymbol)._1().right().get();
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
    public static Module parseMainModuleOuterSyntax(String definitionText, String mainModule) {
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(ParserUtils.class), definitionText, null));
        def.setMainModule(mainModule);
        def.setMainSyntaxModule(mainModule);

        Context context = new Context();
        new CollectProductionsVisitor(context).visitNode(def);

        KILtoKORE kilToKore = new KILtoKORE(context);
        return kilToKore.apply(def).getModule(mainModule).get();
    }

    private static List<org.kframework.kil.Module> slurp(
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories) throws IOException {
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
                    results.addAll(slurp(FileUtils.readFileToString(definitionFile.get()),
                            Sources.fromFile(definitionFile.get()),
                            definitionFile.get().getParentFile(),
                            lookupDirectories));
                else
                    throw KExceptionManager.criticalError("Could not find file: " +
                            definitionFileName + "\nLookup directories:" + allLookupDirectoris, di);
            }
        }
        return results;
    }

    public static Set<Module> loadModules(
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories) throws IOException {

        List<org.kframework.kil.Module> kilModules =
                slurp(definitionText, source, currentDirectory, lookupDirectories);

        Definition def = new Definition();
        def.setItems((List<DefinitionItem>) (Object) kilModules);

        Context context = new Context();
        new CollectProductionsVisitor(context).visitNode(def);

        KILtoKORE kilToKore = new KILtoKORE(context);

        HashMap<String, Module> koreModules = new HashMap<>();
        HashSet<org.kframework.kil.Module> kilModulesSet = new HashSet<>(kilModules);

        kilModules.stream().forEach(m -> kilToKore.apply(m, kilModulesSet, koreModules));

        return new HashSet<>(koreModules.values());
    }

    public static org.kframework.definition.Definition loadDefinition(
            String mainModuleName,
            String syntaxModuleName,
            String definitionText,
            Source source,
            File currentDirectory,
            List<File> lookupDirectories) throws IOException {
        Set<Module> modules = loadModules(definitionText, source, currentDirectory, lookupDirectories);
        Module mainModule = modules.stream().filter(m -> m.name().equals(mainModuleName)).findFirst().get();
        Module syntaxModule = modules.stream().filter(m -> m.name().equals(mainModuleName)).findFirst().get();
        return org.kframework.definition.Definition.apply(mainModule, syntaxModule, immutable(modules), Att());
    }
}

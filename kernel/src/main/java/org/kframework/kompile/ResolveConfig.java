// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.Collections;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.compile.GenerateSentencesFromConfigDecl;
import org.kframework.definition.Bubble;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.kil.Import;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.utils.errorsystem.KEMException;
import scala.collection.Set;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

/**
 * Expands configuration declaration to KORE productions and rules.
 */
class ResolveConfig {
    private final Definition def;
    private final boolean isStrict;
    private final boolean kore;
    private final BiFunction<Module, Bubble, Stream<? extends K>> parseBubble;
    private Function<Module, ParseInModule> getParser;

    ResolveConfig(Definition def, boolean isStrict, boolean kore, BiFunction<Module, Bubble, Stream<? extends K>> parseBubble, Function<Module, ParseInModule> getParser) {
        this.def = def;
        this.isStrict = isStrict;
        this.kore = kore;
        this.parseBubble = parseBubble;
        this.getParser = getParser;
    }

    public Module apply(Module inputModule) {
        if (stream(inputModule.localSentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("config")).count() == 0)
            return inputModule;


        Set<Sentence> importedConfigurationSortsSubsortedToCell = stream(inputModule.productions())
                .filter(p -> p.att().contains("cell"))
                .map(p -> Production(Seq(), Sorts.Cell(), Seq(NonTerminal(p.sort())))).collect(Collections.toSet());

        Module module = Module(inputModule.name(), (Set<Module>) inputModule.imports(),
                (Set<Sentence>) inputModule.localSentences().$bar(importedConfigurationSortsSubsortedToCell),
                inputModule.att());

        ParseInModule parser = getParser.apply(module);

        Set<Sentence> configDeclProductions = stream(module.localSentences())
                .parallel()
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("config"))
                .flatMap(b -> parseBubble.apply(module, b))
                .map(contents -> {
                    KApply configContents = (KApply) contents;
                    List<K> items = configContents.klist().items();
                    switch (configContents.klabel().name()) {
                    case "#ruleNoConditions":
                        return Configuration(items.get(0), BooleanUtils.TRUE, configContents.att());
                    case "#ruleEnsures":
                        return Configuration(items.get(0), items.get(1), configContents.att());
                    default:
                        throw KEMException.compilerError("Illegal configuration with requires clause detected.", configContents);
                    }
                })
                .flatMap(
                        configDecl -> stream(GenerateSentencesFromConfigDecl.gen(configDecl.body(), configDecl.ensures(), configDecl.att(), parser.getExtensionModule(), kore)))
                .collect(Collections.toSet());

        Set<Sentence> configDeclSyntax = stream(configDeclProductions).filter(Sentence::isSyntax).collect(Collections.toSet());
        Set<Sentence> configDeclRules = stream(configDeclProductions).filter(Sentence::isNonSyntax).collect(Collections.toSet());

        if (module.name().endsWith(Import.IMPORTS_SYNTAX_SUFFIX)) {
            Module mapModule;
            if (def.getModule("MAP$SYNTAX").isDefined()) {
                mapModule = def.getModule("MAP$SYNTAX").get();
            } else {
                throw KEMException.compilerError("Module Map must be visible at the configuration declaration, in module " + module.name());
            }
            return Module(module.name(), (Set<Module>) module.imports().$bar(Set(mapModule)),
                    (Set<Sentence>) module.localSentences().$bar(configDeclSyntax),
                    module.att());
        } else {
            Module mapModule;
            if (def.getModule("MAP").isDefined()) {
                mapModule = def.getModule("MAP").get();
            } else {
                throw KEMException.compilerError("Module Map must be visible at the configuration declaration, in module " + module.name());
            }
            return Module(module.name(), (Set<Module>) module.imports().$bar(Set(mapModule)),
                    (Set<Sentence>) module.localSentences().$bar(configDeclRules),
                    module.att());
        }
    }
}

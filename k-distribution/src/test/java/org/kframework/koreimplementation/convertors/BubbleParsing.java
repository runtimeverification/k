// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.koreimplementation.convertors;

import static org.kframework.Collections.immutable;
import static org.kframework.Collections.stream;
import static org.kframework.definition.Constructors.Module;
import static org.kframework.definition.Constructors.Rule;

import java.io.IOException;
import java.net.URL;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.base.Charsets;
import com.google.common.io.Resources;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.kore.K;
import org.kframework.definition.Bubble;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.Grammar;
import org.kframework.parser.concrete2kore.KSyntax2GrammarStatesFilter;
import org.kframework.parser.concrete2kore.Parser;
import org.kframework.parser.concrete2kore.Parser.ParseError;
import org.kframework.parser.concrete2kore.TreeCleanerVisitor;
import org.kframework.parser.outer.Outer;

/**
 * Takes a KORE module with bubble and returns a new KORE module with all
 * the bubbles parsed.
 *
 * Works for KORE bubbles for now.
 *
 * TODO: WORK IN PROGRESS
 */

public class BubbleParsing {

    private Grammar kastGrammar;

    /**
     * TODO: WARNING: paths are hardwired for now.
     */
    public BubbleParsing() {
        Definition kilDefinitionOfKORE = parseUsingOuter(
                BubbleParsing.class.getResource("/convertor-tests/kore.k"));
        KILtoKORE kilToKore1 = new KILtoKORE(null);
        kilDefinitionOfKORE.setMainModule("K");
        org.kframework.definition.Definition definitionOfKORE = kilToKore1.apply(kilDefinitionOfKORE);
        Module kastModule = definitionOfKORE.getModule("K").get();

        kastGrammar = KSyntax2GrammarStatesFilter.getGrammar(kastModule);
    }

    private Definition parseUsingOuter(URL file) {
        Definition def = new Definition();
        String definitionText;
        try {
            definitionText = Resources.toString(file, Charsets.UTF_8);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Sources.generatedBy(BubbleParsing.class), definitionText, null));
        def.setMainModule("KAST");
        def.setMainSyntaxModule("KAST");
        return def;
    }

    /**
     * Replaces the bubbles in m with their parsing.
     */
    public Module parseBubbles(Module m) {
        Set<Module> newImports = stream(m.imports()).map(this::parseBubbles).collect(Collectors.toSet());

        Set<Sentence> newSentences = stream(m.sentences()).map(s -> {
            if (s instanceof Bubble) {
                Bubble bubble = (Bubble) s;

                Parser parser = new Parser(bubble.contents());
                Term parsed = parser.parse(kastGrammar.get("K"), 0);

                if(parsed.equals(Ambiguity.apply())) {
                    ParseError errors = parser.getErrors();
                }

                TreeCleanerVisitor treeCleanerVisitor = new TreeCleanerVisitor();
                Term cleaned = treeCleanerVisitor.apply(parsed).right().get();

                K kBody = TreeNodesToKORE.apply(cleaned);

                switch (bubble.sentenceType()) {
                case "rule":
                    return Rule(kBody, null, null, bubble.att());
                default:
                    return bubble;
                }
            } else {
                return s;
            }
        }).collect(Collectors.toSet());

        return Module(m.name(), immutable(newImports), immutable(newSentences), m.att());
    }
}

// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

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
import org.kframework.Collections;
import org.kframework.kil.Sources;
import org.kframework.kore.K;
import org.kframework.definition.Bubble;
import org.kframework.definition.Module;
import org.kframework.definition.Definition;
import org.kframework.definition.Sentence;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.kernel.Grammar;
import org.kframework.parser.concrete2kore.kernel.KSyntax2GrammarStatesFilter;
import org.kframework.parser.concrete2kore.kernel.Parser;
import org.kframework.parser.concrete2kore.kernel.Parser.ParseError;
import org.kframework.parser.concrete2kore.disambiguation.TreeCleanerVisitor;
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

    private final Grammar.NonTerminal startNonterminal;

    /**
     * Parse bubbles as sort K from module K in the defaulte kore.k
     */
    public BubbleParsing() {
        this("K", "K");
    }

    /**
     * Cusomize start sort and module within the default kore.k.
     * @param mainModule Module containing desired start sort
     * @param startSort Sort to parse bubbles as
     */
    public BubbleParsing(String mainModule, String startSort) {
        this(BubbleParsing.class.getResource("/convertor-tests/kore.k"), mainModule, startSort);
    }

    /**
     * Take grammar from a custom file.
     * @param koreSyntax URL of the file defining the syntax of kore
     * @param mainModule Moudule containing the start sort.
     * @param startSort Sort to parse the bubble as
     */
    public BubbleParsing(URL koreSyntax, String mainModule, String startSort) {
        org.kframework.kil.Definition kilDefinitionOfKORE = parseUsingOuter(koreSyntax);
        kilDefinitionOfKORE.setMainModule(mainModule);
        Definition definitionOfKORE = new KILtoKORE(null).apply(kilDefinitionOfKORE);
        Module kastModule = definitionOfKORE.getModule(mainModule).get();
        startNonterminal = KSyntax2GrammarStatesFilter.getGrammar(kastModule).get(startSort);
    }

    private org.kframework.kil.Definition parseUsingOuter(URL file) {
        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
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

    /** TODO(radu): generalize this function, and eliminate duplicates
     * Replaces the bubbles in m with their parsing.
     */
    public Module parseBubbles(Module m) {
        Set<Module> newImports = stream(m.imports()).map(this::parseBubbles).collect(Collectors.toSet());

        Set<Sentence> newSentences = stream(m.localSentences()).map(s -> {
            if (s instanceof Bubble) {
                Bubble bubble = (Bubble) s;

                Parser parser = new Parser(bubble.contents());
                Term parsed = parser.parse(startNonterminal, 0);

                if(parsed.equals(Ambiguity.apply())) {
                    ParseError errors = parser.getErrors();
                }

                Term cleaned = new TreeCleanerVisitor().apply(parsed).right().get();

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

    /**
     * Parse bubbles in all modules of d.
     */
    public Definition parseBubbles(Definition d) {
        return new Definition(
                d.requires(),
                stream(d.modules()).map(this::parseBubbles).collect(Collections.toSet()),
                d.att());
    }
}

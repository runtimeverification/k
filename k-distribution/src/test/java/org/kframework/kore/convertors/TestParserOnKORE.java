// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.File;
import java.io.IOException;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Test;
import org.kframework.kil.Definition;
import org.kframework.kore.K;
import org.kframework.kore.outer.AbstractVisitor;
import org.kframework.kore.outer.Bubble;
import org.kframework.kore.outer.Module;
import org.kframework.kore.outer.Sentence;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.TreeCleanerVisitor;
import org.kframework.parser.concrete2kore.Grammar;
import org.kframework.parser.concrete2kore.KSyntax2GrammarStatesFilter;
import org.kframework.parser.concrete2kore.Parser;
import org.kframework.utils.errorsystem.ParseFailedException;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.Collections.*;
import scala.util.Either;

public class TestParserOnKORE extends BaseTest {

    class BubbleParsing {

        private Grammar kastGrammar;

        public BubbleParsing() {
            DefintionWithContext foo = parseUsingOuter(new File(ROOT + "/kore.k"));
            KILtoKORE kilToKore1 = new KILtoKORE(foo.context);
            Definition kilDefinitionOfKORE = foo.definition;
            kilDefinitionOfKORE.setMainModule("K");
            org.kframework.kore.outer.Definition definitionOfKORE = kilToKore1.apply(kilDefinitionOfKORE);
            Module kastModule = definitionOfKORE.getModule("K").get();

            kastGrammar = KSyntax2GrammarStatesFilter.getGrammar(kastModule);
        }

        protected Module parseBubbles(Module m) {
            Set<Module> newImports = stream(m.imports()).map(this::parseBubbles).collect(Collectors.toSet());

            Set<Sentence> newSentences = stream(m.sentences()).map(s -> {
                if (s instanceof Bubble) {
                    Bubble bubble = (Bubble) s;

                    Parser parser = new Parser(bubble.contents());
                    Term parsed = parser.parse(kastGrammar.get("K"), 0);

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

    protected String convert(DefintionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        org.kframework.kore.outer.Definition koreDef = kilToKore.apply(defWithContext.definition);

        BubbleParsing bubbleParsing = new BubbleParsing();
        Module koreModule = bubbleParsing.parseBubbles(koreDef.getModule("TEST").get());

        return koreModule.toString();
    }

    @Override
    protected String expectedFilePostfix() {
        return "-expected.k";
    }

    @Test public void simpleRuleKORE() throws IOException {
        outerOnlyTest();
    }

}

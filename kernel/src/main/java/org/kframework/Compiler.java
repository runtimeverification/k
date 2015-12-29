// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework;

import org.kframework.definition.DefinitionTransformer;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.definition.Definition;

/**
 * Contains a curated list of compiler passes.
 * Please only add short code constructing the passes here, not full implementations.
 *
 * The passes are methods with one of the following signatures:
 * Definition -> Definition
 * Module -> Module
 * Sentence -> Sentence
 */

@API
public class Compiler {
    /**
     * Generates the definition appropriate for generating rule parsers.
     */
    public static Definition toRuleParser(Definition d) {
        RuleGrammarGenerator rgg = new RuleGrammarGenerator(d, true);
        return DefinitionTransformer.from(rgg::getRuleGrammar, "roRuleParser").apply(d);
    }
}

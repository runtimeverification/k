// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;

import java.io.Serializable;
import java.util.function.BiFunction;

/**
 * A class representing a compiled definition. It has everything needed for executing and parsing programs.
 */

public class CompiledDefinition implements Serializable {
    public final KompileOptions kompileOptions;
    private final Definition parsedDefinition;
    public final Definition kompiledDefinition;
    private final BiFunction<String, Source, K> programParser;

    public CompiledDefinition(KompileOptions kompileOptions, Definition parsedDefinition, Definition kompiledDefinition, String programStartSymbol) {
        this.kompileOptions = kompileOptions;
        this.parsedDefinition = parsedDefinition;
        this.kompiledDefinition = kompiledDefinition;
        this.programParser = getParser(kompiledDefinition.mainSyntaxModule(), programStartSymbol);
    }

    public CompiledDefinition(KompileOptions kompileOptions, Definition parsedDefinition, Definition kompiledDefinition, BiFunction<String, Source, K> programParser) {
        this.kompileOptions = kompileOptions;
        this.parsedDefinition = parsedDefinition;
        this.kompiledDefinition = kompiledDefinition;
        this.programParser = programParser;
    }

    /**
     * A function that takes a string and the source of that string and parses it as a program into KAST.
     */
    public BiFunction<String, Source, K> getProgramParser() {
        return programParser;
    }

    /**
     * The parsed but uncompiled definition
     */
    public Definition getParsedDefinition() {
        return parsedDefinition;
    }

    /**
     * A module containing the compiled definition
     */
    public Module executionModule() {
        return kompiledDefinition.mainModule();
    }

    public Module syntaxModule() { return kompiledDefinition.mainSyntaxModule(); }

    /**
     * Creates a parser for a module.
     * Will probably want to move the method out of this class here eventually.
     *
     * @return a function taking a String to be parsed, a Source, and returning the parsed string as K.
     */

    public BiFunction<String, Source, K> getParser(Module module, String programStartSymbol) {
        ParseInModule parseInModule = new ParseInModule(getParserModule(module));

        return (BiFunction<String, Source, K> & Serializable) (s, source) -> {
            return TreeNodesToKORE.down(TreeNodesToKORE.apply(parseInModule.parseString(s, programStartSymbol, source)._1().right().get()));
        };
    }

    public Module getParserModule(Module module) {
        return new RuleGrammarGenerator(parsedDefinition).getCombinedGrammar(module);
    }
}

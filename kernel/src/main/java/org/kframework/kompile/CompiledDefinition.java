// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Tuple2;
import scala.util.Either;

import java.io.Serializable;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

/**
 * A class representing a compiled definition. It has everything needed for executing and parsing programs.
 */

public class CompiledDefinition implements Serializable {
    public final KompileOptions kompileOptions;
    private final Definition parsedDefinition;
    public final Definition kompiledDefinition;
    public final Sort programStartSymbol;
    public final KLabel topCellInitializer;

    public CompiledDefinition(KompileOptions kompileOptions, Definition parsedDefinition, Definition kompiledDefinition, Sort programStartSymbol, KLabel topCellInitializer) {
        this.kompileOptions = kompileOptions;
        this.parsedDefinition = parsedDefinition;
        this.kompiledDefinition = kompiledDefinition;
        this.programStartSymbol = programStartSymbol;
        this.topCellInitializer = topCellInitializer;
    }

    /**
     * A function that takes a string and the source of that string and parses it as a program into KAST.
     */
    public BiFunction<String, Source, K> getProgramParser(KExceptionManager kem) {
        return getParser(kompiledDefinition.mainSyntaxModule(), programStartSymbol, kem);
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

    public BiFunction<String, Source, K> getParser(Module module, Sort programStartSymbol, KExceptionManager kem) {
        ParseInModule parseInModule = new ParseInModule(getParserModule(module), kompileOptions.strict());

        return (BiFunction<String, Source, K> & Serializable) (s, source) -> {
            Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> res = parseInModule.parseString(s, programStartSymbol, source);
            kem.addAllKException(res._2().stream().map(e -> e.getKException()).collect(Collectors.toSet()));
            if (res._1().isLeft()) {
                throw res._1().left().get().iterator().next();
            }
            return TreeNodesToKORE.down(TreeNodesToKORE.apply(res._1().right().get()));
        };
    }

    public Module getParserModule(Module module) {
        return new RuleGrammarGenerator(parsedDefinition).getCombinedGrammar(module);
    }
}

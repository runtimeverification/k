// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.concrete2kore.disambiguation.AmbFilter;
import org.kframework.parser.concrete2kore.disambiguation.CorrectCastPriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.CorrectKSeqPriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.CorrectRewritePriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.PreferAvoidVisitor;
import org.kframework.parser.concrete2kore.disambiguation.PriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.RemoveBracketVisitor;
import org.kframework.parser.concrete2kore.disambiguation.TreeCleanerVisitor;
import org.kframework.parser.concrete2kore.disambiguation.VariableTypeInferenceFilter;
import org.kframework.parser.concrete2kore.kernel.Grammar;
import org.kframework.parser.concrete2kore.kernel.KSyntax2GrammarStatesFilter;
import org.kframework.parser.concrete2kore.kernel.Parser;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.io.Serializable;
import java.util.Collections;
import java.util.Set;

/**
 * A wrapper that takes a module and one can call the parser
 * for that module in thread safe way.
 * Declarative disambiguation filters are also applied.
 */
public class ParseInModule implements Serializable {
    private final Module module;
    private final Grammar grammar;
    public ParseInModule(Module module) {
        this.module = module;
        this.grammar = KSyntax2GrammarStatesFilter.getGrammar(module);
    }

    public Module module() {
        return module;
    }

    /**
     * Parse as input the given string and start symbol using the module stored in the object.
     * @param input          the string to parse.
     * @param startSymbol    the start symbol from which to parse.
     * @return the Term representation of the parsed input.
     */
    // TODO: figure out how to handle parsing errors
    public Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>>
            parseString(CharSequence input, String startSymbol, Source source) {
        return parseString(input, startSymbol, source, 1, 1);
    }

    public Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>>
            parseString(CharSequence input, String startSymbol, Source source, int startLine, int startColumn) {
        Parser parser = new Parser(input, source, startLine, startColumn);
        Term parsed;
        try {
            parsed = parser.parse(grammar.get(startSymbol), 0);
        } catch (ParseFailedException e) {
            return Tuple2.apply(Left.apply(Collections.singleton(e)), Collections.emptySet());
        }

        if (parsed.equals(Ambiguity.apply())) {
            Parser.ParseError errors = parser.getErrors();
            throw new AssertionError("There are parsing errors: " + errors.toString());
        }
        Set<ParseFailedException> warn = new AmbFilter().warningUnit();

        Either<Set<ParseFailedException>, Term> rez = new TreeCleanerVisitor().apply(parsed);
        if (rez.isLeft())
            return new Tuple2<>(rez, warn);
        rez = new CorrectRewritePriorityVisitor().apply(rez.right().get());
        if (rez.isLeft())
            return new Tuple2<>(rez, warn);
        rez = new CorrectKSeqPriorityVisitor().apply(rez.right().get());
        if (rez.isLeft())
            return new Tuple2<>(rez, warn);
        rez = new CorrectCastPriorityVisitor().apply(rez.right().get());
        if (rez.isLeft())
            return new Tuple2<>(rez, warn);
        rez = new PriorityVisitor(module.priorities(), module.leftAssoc(), module.rightAssoc()).apply(rez.right().get());
        if (rez.isLeft())
            return new Tuple2<>(rez, warn);
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rez2 = new VariableTypeInferenceFilter(module.subsorts(), module.definedSorts()).apply(rez.right().get());
        if (rez2._1().isLeft())
            return rez2;
        warn = rez2._2();

        Term rez3 = new PreferAvoidVisitor().apply(rez2._1().right().get());
        rez2 = new AmbFilter().apply(rez3);
        warn = new AmbFilter().mergeWarnings(rez2._2(), warn);
        rez3 = new RemoveBracketVisitor().apply(rez2._1().right().get());

        return new Tuple2<>(Right.apply(rez3), warn);
    }
}

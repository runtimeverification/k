// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import com.google.common.collect.Sets;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kore.Sort;
import org.kframework.parser.Term;
import org.kframework.parser.concrete2kore.disambiguation.AmbFilter;
import org.kframework.parser.concrete2kore.disambiguation.ApplyTypeCheckVisitor;
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
import org.kframework.utils.errorsystem.KException;
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
    private Module module;
    private final Module disambModule;
    private final Module parsingModule;
    private final Grammar grammar;
    public ParseInModule(Module module) {
        this.module = module;
        this.disambModule = module;
        this.parsingModule = module;
        this.grammar = KSyntax2GrammarStatesFilter.getGrammar(parsingModule);
    }

    public ParseInModule(Module module, Module disambModule, Module parsingModule) {
        this.module = module;
        this.disambModule = disambModule;
        this.parsingModule = parsingModule;
        this.grammar = KSyntax2GrammarStatesFilter.getGrammar(parsingModule);
    }

    /**
     * The original before any processing has been done. This can be used to invalidate caches.
     * @return Module given by the user.
     */
    public Module module() {
        return module;
    }

    public void setModule(Module module) {
        this.module = module;
    }

    /**
     * The module in which parsing will be done.
     * Note that this module will be used for disambiguation, and the parsing module can be different.
     * This allows for grammar rewriting and more flexibility in the implementation.
     * @return Module in which parsing will be done.
     */
    public Module disambModule() {
        return disambModule;
    }

    /**
     * The exact module used for parsing. This can contain productions and sorts that are not
     * necessarily representable in KORE (sorts like Ne#Ids, to avoid name collisions).
     * In this case the modified productino will be annotated with the information from the
     * original production, so disambiguation can be done safely.
     * @return Module used to parse with.
     */
    // TODO: (radum) I'm not sure yet if this should be available outside this class
    //public Module getParsingModule() {
    //   return parsingModule;
    //}

    /**
     * Parse as input the given string and start symbol using the module stored in the object.
     * @param input          the string to parse.
     * @param startSymbol    the start symbol from which to parse.
     * @return the Term representation of the parsed input.
     */
    public Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>>
            parseString(String input, Sort startSymbol, Source source) {
        return parseString(input, startSymbol, source, 1, 1);
    }

    public Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>>
            parseString(String input, Sort startSymbol, Source source, int startLine, int startColumn) {
        Grammar.NonTerminal startSymbolNT = grammar.get(startSymbol.name());
        Set<ParseFailedException> warn = new AmbFilter().warningUnit();
        if (startSymbolNT == null) {
            String msg = "Could not find start symbol: " + startSymbol;
            KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg);
            return new Tuple2<>(Left.apply(Sets.newHashSet(new ParseFailedException(kex))), warn);
        }

        Parser parser = new Parser(input, source, startLine, startColumn);
        Term parsed;
        try {
            parsed = parser.parse(startSymbolNT, 0);
        } catch (ParseFailedException e) {
            return Tuple2.apply(Left.apply(Collections.singleton(e)), Collections.emptySet());
        }

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
        rez = new ApplyTypeCheckVisitor(disambModule.subsorts()).apply(rez.right().get());
        if (rez.isLeft())
            return new Tuple2<>(rez, warn);
        rez = new PriorityVisitor(disambModule.priorities(), disambModule.leftAssoc(), disambModule.rightAssoc()).apply(rez.right().get());
        if (rez.isLeft())
            return new Tuple2<>(rez, warn);
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rez2 = new VariableTypeInferenceFilter(disambModule.subsorts(), disambModule.definedSorts(), disambModule.productionsFor()).apply(rez.right().get());
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

package org.kframework.parser.concrete2kore;

import org.kframework.kore.outer.Module;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.concrete2kore.disambiguation.CorrectCastPriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.CorrectKSeqPriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.CorrectRewritePriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.PreferAvoidVisitor;
import org.kframework.parser.concrete2kore.disambiguation.PriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.TreeCleanerVisitor;
import org.kframework.parser.concrete2kore.kernel.Grammar;
import org.kframework.parser.concrete2kore.kernel.KSyntax2GrammarStatesFilter;
import org.kframework.parser.concrete2kore.kernel.Parser;

/**
 * A wrapper that takes a module and one can call the parser
 * for that module in thread safe way.
 * Declarative disambiguation filters are also applied.
 */
public class ParseInModule {
    private final Module module;
    private final Grammar grammar;
    public ParseInModule(Module module) {
        this.module = module;
        this.grammar = KSyntax2GrammarStatesFilter.getGrammar(module);
    }

    /**
     * Parse as input the given string and start symbol using the module stored in the object.
     * @param input          the string to parse.
     * @param startSymbol    the start symbol from which to parse.
     * @return the Term representation of the parsed input.
     */
    // TODO: require source location to this call
    // TODO: figure out how to handle parsing errors
    public Term parseString(CharSequence input, String startSymbol) {
        Parser parser = new Parser(input);
        Term parsed = parser.parse(grammar.get(startSymbol), 0);

        if (parsed.equals(Ambiguity.apply())) {
            Parser.ParseError errors = parser.getErrors();
            throw new AssertionError("There are parsing errors: " + errors.toString());
        }

        Term cleaned = new TreeCleanerVisitor().apply(parsed).right().get();
        cleaned = new CorrectRewritePriorityVisitor().apply(cleaned).right().get();
        cleaned = new CorrectKSeqPriorityVisitor().apply(cleaned).right().get();
        cleaned = new CorrectCastPriorityVisitor().apply(cleaned).right().get();
        cleaned = new PriorityVisitor(module.priorities(), module.leftAssoc(), module.rightAssoc()).apply(cleaned).right().get();

        cleaned = new PreferAvoidVisitor().apply(cleaned);

        return cleaned;
    }
}

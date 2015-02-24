package org.kframework.parser.concrete2kore.generator;

import org.kframework.kore.Sort;
import org.kframework.kore.outer.Module;
import org.kframework.kore.outer.Sentence;
import org.kframework.parser.concrete2kore.ParseInModule;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.kore.Constructors.*;
import static org.kframework.kore.outer.Constructors.*;

/**
 * Generator for rule and ground parsers.
 * Takes as input a reference to a definition containing all the base syntax of K
 * and uses it to generate a grammar by connecting all users sorts in a lattice with
 * the top sort KItem#Top and the bottom sort KItem#Bottom.
 *
 * The instances of the non-terminal KItem is renamed in KItem#Top if found in the right
 * hand side of a production, and into KItem#Bottom if found in the left hand side.
 */
public class RuleGrammarGenerator {

    private final Module baseK;
    private static final Sort KBott = Sort("KBott");
    private static final Sort KSort = Sort("K");

    public RuleGrammarGenerator(Module baseK) {
        this.baseK = renameKItem2Bottom(baseK);
    }

    private Module renameKItem2Bottom(Module def) {
        // TODO: do renaming of KItem and K in the LHS to KBott
        return def;
    }

    public ParseInModule getRuleGrammar(Module mod) {
        // TODO: do some changes to the module
        Set<Sentence> prods = new HashSet<>();

        // create the diamond
        for (Sort srt : iterable(mod.definedSorts())) {
            // Sort ::= KBott
            prods.add(SyntaxProduction(srt, Seq(NonTerminal(KBott)), Attributes()));
            // K ::= Sort
            prods.add(SyntaxProduction(KSort, Seq(NonTerminal(srt)), Attributes()));
        }

        Module newM = new Module(mod.name() + "-RULES", Set(mod, baseK), immutable(prods), null);
        return new ParseInModule(newM);
    }
}

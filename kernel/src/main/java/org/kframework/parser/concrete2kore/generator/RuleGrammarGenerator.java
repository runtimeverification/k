// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.generator;

import org.kframework.attributes.Att;
import org.kframework.kore.Sort;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.parser.concrete2kore.ParseInModule;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.definition.Constructors.*;

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
    private static final Sort KTop = Sort("K");
    private static final Set<Sort> kSorts = new HashSet<>();;

    public RuleGrammarGenerator(Module baseK) {
        this.baseK = renameKItem2Bottom(baseK);
        kSorts.add(KBott);
        kSorts.add(KTop);
        kSorts.add(Sort("KLabel"));
        kSorts.add(Sort("KList"));
        kSorts.add(Sort("KItem"));
    }

    private Module renameKItem2Bottom(Module def) {
        // TODO: do renaming of KItem and K in the LHS to KBott
        return def;
    }

    /**
     * Create the rule parser for the given module.
     * It creates a module which includes the given module and the base K module given to the
     * constructor. The new module contains syntax declaration for Casts and the diamond
     * which connects the user concrete syntax with K syntax.
     * @param mod    module for which to create the parser.
     * @return parser which applies disambiguation filters by default.
     */
    public ParseInModule getRuleGrammar(Module mod) {
        Set<Sentence> prods = new HashSet<>();

        // create the diamond
        for (Sort srt : iterable(mod.definedSorts())) {
            if (!kSorts.contains(srt)) {
                // Sort ::= KBott
                prods.add(Production(srt, Seq(NonTerminal(KBott)), Att()));
                // K ::= Sort
                prods.add(Production(KTop, Seq(NonTerminal(srt)), Att()));
                // K ::= K "::Sort" | K ":Sort" | K "<:Sort" | K ":>Sort"
                Att attrs1 = Att().add("sort", srt.name());
                prods.add(Production("#SyntacticCast", KBott, Seq(NonTerminal(KTop), RegexTerminal("::" + srt.name() + "(?![a-zA-Z0-9])")), attrs1));
                Att attrs2 = Att().add("sort", srt.name());
                prods.add(Production("#SemanticCast", KBott, Seq(NonTerminal(KTop), RegexTerminal(":" + srt.name() + "(?![a-zA-Z0-9])")), attrs2));
                Att attrs3 = Att().add("sort", srt.name());
                prods.add(Production("#InnerCast", KBott, Seq(NonTerminal(KTop), RegexTerminal("<:" + srt.name() + "(?![a-zA-Z0-9])")), attrs3));
                Att attrs4 = Att().add("sort", srt.name());
                prods.add(Production("#OuterCast", KBott, Seq(NonTerminal(KTop), RegexTerminal(":>" + srt.name() + "(?![a-zA-Z0-9])")), attrs4));
            }
        }

        Module newM = new Module(mod.name() + "-RULES", Set(mod, baseK), immutable(prods), null);
        return new ParseInModule(newM);
    }
}

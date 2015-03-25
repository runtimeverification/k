// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.generator;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.definition.Production;
import org.kframework.kore.Sort;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.parser.concrete2kore.ParseInModule;
import scala.Function1;

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
    private static final Sort KLabel = Sort("KLabel");
    private static final Sort KList = Sort("KList");
    private static final Sort KItem = Sort("KItem");
    private static final Set<Sort> kSorts = new HashSet<>();
    static {
        kSorts.add(KBott);
        kSorts.add(KTop);
        kSorts.add(KLabel);
        kSorts.add(KList);
        kSorts.add(KItem);
        kSorts.add(Sort("RuleContent"));
        kSorts.add(Sort("#CellName"));
        kSorts.add(Sort("KVariable"));
    }

    public RuleGrammarGenerator(Module baseK) {
        this.baseK = renameKItem2Bottom(baseK);
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
                prods.addAll(makeCasts(KBott, KTop, srt));
            }
        }
        prods.addAll(makeCasts(KLabel, KLabel, KLabel));
        prods.addAll(makeCasts(KList, KList, KList));
        prods.addAll(makeCasts(KBott, KTop, KItem));

        scala.collection.immutable.Set<Sentence> prods2 = stream(mod.sentences()).filter(p -> !(p instanceof Production && p.att().contains("cell"))).collect(Collections.toSet());
        Module noCells = new Module(mod.name() + "-NO-CELLS", Set(), prods2, null);

        Module newM = new Module(mod.name() + "-RULES", Set(noCells, baseK), immutable(prods), null);
        return new ParseInModule(newM);
    }

    private Set<Sentence> makeCasts(Sort outerSort, Sort innerSort, Sort castSort) {
        Set<Sentence> prods = new HashSet<>();
        Att attrs1 = Att().add("sort", castSort.name());
        prods.add(Production("#SyntacticCast", outerSort, Seq(NonTerminal(innerSort), RegexTerminal("::" + castSort.name() + "(?![a-zA-Z0-9])")), attrs1));
        prods.add(Production("#SemanticCast",  outerSort, Seq(NonTerminal(innerSort), RegexTerminal(":"  + castSort.name() + "(?![a-zA-Z0-9])")), attrs1));
        prods.add(Production("#InnerCast",     outerSort, Seq(NonTerminal(innerSort), RegexTerminal("<:" + castSort.name() + "(?![a-zA-Z0-9])")), attrs1));
        prods.add(Production("#OuterCast",     outerSort, Seq(NonTerminal(innerSort), RegexTerminal(":>" + castSort.name() + "(?![a-zA-Z0-9])")), attrs1));
        return prods;
    }

    public static ParseInModule getProgramsGrammar(Module mod) {
        Set<Sentence> prods = new HashSet<>();

        // if no start symbol has been defined in the configuration, then use K
        for (Sort srt : iterable(mod.definedSorts())) {
            if (!kSorts.contains(srt) && !mod.listSorts().contains(srt)) {
                // K ::= Sort
                prods.add(Production(KTop, Seq(NonTerminal(srt)), Att()));
            }
        }

        Module newM = new Module(mod.name() + "-FOR-PROGRAMS", Set(mod), immutable(prods), null);
        return new ParseInModule(newM);
    }
}

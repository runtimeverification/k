// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.generator;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.definition.Definition;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Terminal;
import org.kframework.kore.Sort;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.parser.concrete2kore.ParseInModule;
import scala.Function1;
import scala.collection.immutable.Seq;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.definition.Constructors.*;

/**
 * Generator for rule and ground parsers.
 * Takes as input a reference to a definition containing all the base syntax of K
 * and uses it to generate a grammar by connecting all users sorts in a lattice with
 * the top sort KItem#Top and the bottom sort KItem#Bottom.
 * <p/>
 * The instances of the non-terminal KItem is renamed in KItem#Top if found in the right
 * hand side of a production, and into KItem#Bottom if found in the left hand side.
 */
public class RuleGrammarGenerator {

    private final Map<String, Module> baseK;
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
        kSorts.add(Sort("KVariable"));
    }

    public RuleGrammarGenerator(Set<Module> baseK) {
        this.baseK = new HashMap<>();
        renameKItem2Bottom(baseK).stream().forEach(m -> this.baseK.put(m.name(), m));
    }

    private Set<Module> renameKItem2Bottom(Set<Module> def) {
        // TODO: do renaming of KItem and K in the LHS to KBott
        return def;
    }

    public ParseInModule getRuleGrammar(Module mod) {
        return getCombinedGrammar(mod, "RULE-CELLS");
    }

    public ParseInModule getConfigGrammar(Module mod) {
        return getCombinedGrammar(mod, "CONFIG-CELLS");
    }

    /**
     * Create the rule parser for the given module.
     * It creates a module which includes the given module and the base K module given to the
     * constructor. The new module contains syntax declaration for Casts and the diamond
     * which connects the user concrete syntax with K syntax.
     *
     * @param mod module for which to create the parser.
     * @return parser which applies disambiguation filters by default.
     */
    public ParseInModule getCombinedGrammar(Module mod, String cellModule) {
        Set<Sentence> prods = new HashSet<>();

        // create the diamond
        for (Sort srt : iterable(mod.definedSorts())) {
            if (!kSorts.contains(srt) && !srt.name().startsWith("#")) {
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
        prods.addAll(makeCasts(KBott, KTop, KTop));

        scala.collection.immutable.Set<Sentence> prods2 = stream(mod.sentences()).map(s -> {
            if (s instanceof Production && (s.att().contains("cell") || s.att().contains("maincell"))) {
                Production p = (Production) s;
                // assuming that productions tagged with 'cell' start and end with terminals, and only have non-terminals in the middle
                assert p.items().head() instanceof Terminal || p.items().head() instanceof RegexTerminal;
                assert p.items().last() instanceof Terminal || p.items().last() instanceof RegexTerminal;
                Seq<ProductionItem> pi = Seq(p.items().head(), NonTerminal(Sort("#OptionalDots")), NonTerminal(Sort("K")), NonTerminal(Sort("#OptionalDots")), p.items().last());
                return Production(p.klabel().get().name(), Sort("Cell"), pi, p.att());
            }
            return s;
        }).collect(Collections.toSet());
        Module noCells = new Module(mod.name() + "-NO-CELLS", Set(baseK.getModule(cellModule).get()), prods2, null);

        Module newM = new Module(mod.name() + "-" + cellModule, Set(noCells, baseK.getModule("K").get(), baseK.getModule(cellModule).get()), immutable(prods), null);
        return new ParseInModule(newM);
    }

    private Set<Sentence> makeCasts(Sort outerSort, Sort innerSort, Sort castSort) {
        Set<Sentence> prods = new HashSet<>();
        Att attrs1 = Att().add("sort", castSort.name());
        prods.add(Production("#SyntacticCast", castSort, Seq(NonTerminal(castSort), Terminal("::" + castSort.name())), attrs1));
        prods.add(Production("#SemanticCast", castSort, Seq(NonTerminal(castSort), Terminal(":" + castSort.name())), attrs1));
        prods.add(Production("#InnerCast", outerSort, Seq(NonTerminal(castSort), Terminal("<:" + castSort.name())), attrs1));
        prods.add(Production("#OuterCast", castSort, Seq(NonTerminal(innerSort), Terminal(":>" + castSort.name())), attrs1));
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

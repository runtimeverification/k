// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.generator;

import org.apache.commons.collections4.trie.PatriciaTrie;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Sentence;
import org.kframework.definition.Terminal;
import org.kframework.definition.UserList;
import org.kframework.kil.Attribute;
import org.kframework.kil.loader.Constants;
import org.kframework.kore.Sort;
import org.kframework.parser.concrete2kore.ParseInModule;
import scala.collection.Seq;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;
import static scala.compat.java8.JFunction.*;

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

    private final Definition baseK;
    private final boolean strict;
    private static final Set<Sort> kSorts = new HashSet<>();

    static {
        kSorts.add(Sorts.KBott());
        kSorts.add(Sorts.K());
        kSorts.add(Sorts.KLabel());
        kSorts.add(Sorts.KList());
        kSorts.add(Sorts.KItem());
        kSorts.add(Sort("RuleContent"));
        kSorts.add(Sort("KConfigVar"));
        kSorts.add(Sorts.KString());
    }

    private static Set<Sort> kSorts() {
        return java.util.Collections.unmodifiableSet(kSorts);
    }
    /// modules that have a meaning:
    public static final String RULE_CELLS = "RULE-CELLS";
    public static final String CONFIG_CELLS = "CONFIG-CELLS";
    public static final String K = "K";
    public static final String AUTO_CASTS = "AUTO-CASTS";
    public static final String KSEQ_SYMBOLIC = "KSEQ-SYMBOLIC";
    public static final String K_TOP_SORT = "K-TOP-SORT";
    public static final String K_BOTTOM_SORT = "K-BOTTOM-SORT";
    public static final String AUTO_FOLLOW = "AUTO-FOLLOW";
    public static final String PROGRAM_LISTS = "PROGRAM-LISTS";
    public static final String RULE_LISTS = "RULE-LISTS";

    public static final String POSTFIX = "-PROGRAM-PARSING";

    public static final String ID = "ID";
    public static final String ID_PROGRAM_PARSING = ID + POSTFIX;

    /**
     * Initialize a grammar generator.
     * @param baseK A Definition containing a K module giving the syntax of K itself.
     *              The default K syntax is defined in include/kast.k.
     * @param strict true if the generated parsers should retain inferred variable
     *               sorts as sort predicate in the requires clause.
     */
    public RuleGrammarGenerator(Definition baseK, boolean strict) {
        this.baseK = baseK;
        this.strict = strict;
    }

    private Set<Module> renameKItem2Bottom(Set<Module> def) {
        // TODO: do renaming of KItem and K in the LHS to KBott?
        return def;
    }

    /**
     * Creates the seed module that can be used to parse rules.
     * Imports module markers RULE-CELLS and K found in /include/kast.k.
     * @param mod The user defined module from which to start.
     * @return a new module which imports the original user module and a set of marker modules.
     */
    public Module getRuleGrammar(Module mod) {
        // import RULE-CELLS in order to parse cells specific to rules
        Module newM = new Module(mod.name() + "-" + RULE_CELLS, Set(mod, baseK.getModule(K).get(), baseK.getModule(RULE_CELLS).get()), Set(), Att());
        return newM;
    }

    /**
     * Creates the seed module that can be used to parse configurations.
     * Imports module markers CONFIG-CELLS and K found in /include/kast.k.
     * @param mod The user defined module from which to start.
     * @return a new module which imports the original user module and a set of marker modules.
     */
    public Module getConfigGrammar(Module mod) {
        // import CONFIG-CELLS in order to parse cells specific to configurations
        Module newM = new Module(mod.name() + "-" + CONFIG_CELLS, Set(mod, baseK.getModule(K).get(), baseK.getModule(CONFIG_CELLS).get()), Set(), Att());
        return newM;
    }

    /**
     * Creates the seed module that can be used to parse programs.
     * Imports module markers PROGRAM-LISTS found in /include/kast.k.
     * @param mod The user defined module from which to start.
     * @return a new module which imports the original user module and a set of marker modules.
     */
    public Module getProgramsGrammar(Module mod) {

        if(mod.name().endsWith(POSTFIX)) {
            return mod;
        } else {
            // import PROGRAM-LISTS so user lists are modified to parse programs
            scala.collection.Set<Module> modules = Set(mod, baseK.getModule(PROGRAM_LISTS).get());

            if (stream(mod.importedModules()).anyMatch(m -> m.name().equals(ID))) {
                Module idProgramParsingModule = baseK.getModule(ID_PROGRAM_PARSING).get();
                modules = add(idProgramParsingModule, modules);
            }

            return Module.apply(mod.name() + POSTFIX, modules, Set(), Att());
        }
    }

    public static boolean isParserSort(Sort s) {
        return kSorts.contains(s) || s.name().startsWith("#");
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
    public ParseInModule getCombinedGrammar(Module mod) {
        Set<Sentence> prods = new HashSet<>();
        Set<Sentence> extensionProds = new HashSet<>();
        Set<Sentence> disambProds;

        if (baseK.getModule(AUTO_CASTS).isDefined() && mod.importedModules().contains(baseK.getModule(AUTO_CASTS).get())) { // create the diamond
            Set<Sentence> temp;
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!isParserSort(srt)) {
                    // K ::= K "::Sort" | K ":Sort" | K "<:Sort" | K ":>Sort"
                    prods.addAll(makeCasts(Sorts.KBott(), Sorts.K(), srt));
                }
            }
            prods.addAll(makeCasts(Sorts.KLabel(), Sorts.KLabel(), Sorts.KLabel()));
            prods.addAll(makeCasts(Sorts.KList(), Sorts.KList(), Sorts.KList()));
            prods.addAll(makeCasts(Sorts.KBott(), Sorts.K(), Sorts.KItem()));
            prods.addAll(makeCasts(Sorts.KBott(), Sorts.K(), Sorts.K()));
        }
        if (baseK.getModule(K_TOP_SORT).isDefined() && mod.importedModules().contains(baseK.getModule(K_TOP_SORT).get())) { // create the diamond
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!isParserSort(srt)) {
                    // K ::= Sort
                    prods.add(Production(Sorts.K(), Seq(NonTerminal(srt)), Att()));
                }
            }
        }

        if (baseK.getModule(K_BOTTOM_SORT).isDefined() && mod.importedModules().contains(baseK.getModule(K_BOTTOM_SORT).get())) { // create the diamond
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!isParserSort(srt)) {
                    // Sort ::= KBott
                    prods.add(Production(srt, Seq(NonTerminal(Sorts.KBott())), Att()));
                }
            }
        }

        if (baseK.getModule(K).isDefined() && mod.importedModules().contains(baseK.getModule(K).get())) {
            Production rewrite = stream(baseK.getModule(K).get().productionsFor().apply(KLabel("#KRewrite"))).findAny().get();
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!isParserSort(srt)) {
                    prods.add(Production(srt, Seq(NonTerminal(srt), Terminal("=>"), NonTerminal(srt)), Att().add(Constants.ORIGINAL_PRD, Production.class, rewrite)));
                }
            }
        }



        if (baseK.getModule(KSEQ_SYMBOLIC).isDefined() && mod.importedModules().contains(baseK.getModule(KSEQ_SYMBOLIC).get())) {
            Production as = stream(baseK.getModule(KSEQ_SYMBOLIC).get().productionsFor().apply(KLabel("#KAs"))).findAny().get();
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!isParserSort(srt)) {
                    prods.add(Production(srt, Seq(NonTerminal(srt), Terminal("#as"), NonTerminal(srt)), Att().add(Constants.ORIGINAL_PRD, Production.class, as)));
                }
            }
        }
        extensionProds.addAll(prods);

        boolean addRuleCells;
        if (baseK.getModule(RULE_CELLS).isDefined() && mod.importedModules().contains(baseK.getModule(RULE_CELLS).get())) { // prepare cell productions for rule parsing
            // make sure a configuration actually exists, otherwise ConfigurationInfoFromModule explodes.
            addRuleCells = mod.sentences().exists(func(p -> p instanceof Production && ((Production) p).att().contains("cell")));
        } else {
            addRuleCells = false;
        }
        Set<Sentence> parseProds;
        if (addRuleCells) {
            ConfigurationInfo cfgInfo = new ConfigurationInfoFromModule(mod);
            parseProds = Stream.concat(prods.stream(), stream(mod.sentences())).flatMap(s -> {
                if (s instanceof Production && s.att().contains("cellCollection")) {
                    return Stream.empty();
                }
                if (s instanceof Production && (s.att().contains("cell"))) {
                    Production p = (Production) s;
                    // assuming that productions tagged with 'cell' start and end with terminals, and only have non-terminals in the middle
                    assert p.items().head() instanceof Terminal || p.items().head() instanceof RegexTerminal;
                    assert p.items().last() instanceof Terminal || p.items().last() instanceof RegexTerminal;
                    final ProductionItem body;
                    if (cfgInfo.isLeafCell(p.sort())) {
                        body = p.items().tail().head();
                    } else {
                        body = NonTerminal(Sort("Bag"));
                    }
                    final ProductionItem optDots = NonTerminal(Sort("#OptionalDots"));
                    Seq<ProductionItem> pi = Seq(p.items().head(), optDots, body, optDots, p.items().last());
                    Production p1 = Production(p.klabel().get().name(), p.sort(), pi, p.att());
                    Production p2 = Production(Sort("Cell"), Seq(NonTerminal(p.sort())));
                    return Stream.of(p1, p2);
                }
                if (s instanceof Production && (s.att().contains("cellFragment"))) {
                    Production p = (Production) s;
                    Production p1 = Production(Sort("Cell"), Seq(NonTerminal(p.sort())));
                    return Stream.of(p, p1);
                }
                return Stream.of(s);
            }).collect(Collectors.toSet());
        } else
            parseProds = Stream.concat(prods.stream(), stream(mod.sentences())).collect(Collectors.toSet());

        if (baseK.getModule(AUTO_FOLLOW).isDefined() && mod.importedModules().contains(baseK.getModule(AUTO_FOLLOW).get())) {
            Object PRESENT = new Object();
            PatriciaTrie<Object> terminals = new PatriciaTrie<>(); // collect all terminals so we can do automatic follow restriction for prefix terminals
            parseProds.stream().filter(sent -> sent instanceof Production).forEach(p -> stream(((Production) p).items()).forEach(i -> {
                if (i instanceof Terminal) terminals.put(((Terminal) i).value(), PRESENT);
            }));
            parseProds = parseProds.stream().map(s -> {
                if (s instanceof Production) {
                    Production p = (Production) s;
                    if (p.sort().name().startsWith("#"))
                        return p; // don't do anything for such productions since they are advanced features
                    // rewrite productions to contain follow restrictions for prefix terminals
                    // example _==_ and _==K_ can produce ambiguities. Rewrite the first into _(==(?![K])_
                    // this also takes care of casting and productions that have ":"
                    if (p.klabel().isDefined())
                        p = Production(p.klabel().get().name(), p.sort(), p.items(), p.att());
                    else
                        p = Production(p.sort(), p.items(), p.att());
                    return p;
                }
                return s;
            }).collect(Collectors.toSet());
        }

        disambProds = parseProds.stream().collect(Collectors.toSet());
        if (baseK.getModule(PROGRAM_LISTS).isDefined() && mod.importedModules().contains(baseK.getModule(PROGRAM_LISTS).get())) {
            Set<Sentence> prods3 = new HashSet<>();
            // if no start symbol has been defined in the configuration, then use K
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!kSorts.contains(srt) && !mod.listSorts().contains(srt)) {
                    // K ::= Sort
                    prods3.add(Production(Sorts.K(), Seq(NonTerminal(srt)), Att()));
                }
            }
            // for each triple, generate a new pattern which works better for parsing lists in programs.
            prods3.addAll(parseProds.stream().collect(Collectors.toSet()));
            java.util.Set<Sentence> res = new HashSet<>();
            for (UserList ul : UserList.getLists(prods3)) {
                org.kframework.definition.Production prod1, prod2, prod3, prod4, prod5;

                Att newAtts = ul.attrs.remove("userList");
                // Es#Terminator ::= "" [klabel('.Es)]
                prod1 = Production(ul.terminatorKLabel, Sort(ul.sort + "#Terminator"), Seq(Terminal("")),
                        newAtts.add("klabel", ul.terminatorKLabel).add(Constants.ORIGINAL_PRD, Production.class, ul.pTerminator));
                // Ne#Es ::= E "," Ne#Es [klabel('_,_)]
                prod2 = Production(ul.klabel, Sort("Ne#" + ul.sort),
                        Seq(NonTerminal(Sort(ul.childSort)), Terminal(ul.separator), NonTerminal(Sort("Ne#" + ul.sort))),
                        newAtts.add("klabel", ul.klabel).add(Constants.ORIGINAL_PRD, Production.class, ul.pList));
                // Ne#Es ::= E Es#Terminator [klabel('_,_)]
                prod3 = Production(ul.klabel, Sort("Ne#" + ul.sort),
                        Seq(NonTerminal(Sort(ul.childSort)), NonTerminal(Sort(ul.sort + "#Terminator"))),
                        newAtts.add("klabel", ul.klabel).add(Constants.ORIGINAL_PRD, Production.class, ul.pList));
                // Es ::= Ne#Es
                prod4 = Production(Sort(ul.sort), Seq(NonTerminal(Sort("Ne#" + ul.sort))));
                // Es ::= Es#Terminator // if the list is *
                prod5 = Production(Sort(ul.sort), Seq(NonTerminal(Sort(ul.sort + "#Terminator"))));

                res.add(prod1);
                res.add(prod2);
                res.add(prod3);
                res.add(prod4);
                res.add(SyntaxSort(Sort(ul.sort + "#Terminator")));
                res.add(SyntaxSort(Sort("Ne#" + ul.sort)));
                if (!ul.nonEmpty) {
                    res.add(prod5);
                }
            }
            res.addAll(prods3.stream().filter(p -> !(p instanceof Production && (p.att().contains(Att.generatedByListSubsorting()) || p.att().contains(Att.userList())))).collect(Collectors.toSet()));
            parseProds = res;
        }

        if (baseK.getModule(RULE_LISTS).isDefined() && mod.importedModules().contains(baseK.getModule(RULE_LISTS).get())) {
            java.util.Set<Sentence> res = new HashSet<>();
            for (UserList ul : UserList.getLists(parseProds)) {
                org.kframework.definition.Production prod1;
                // Es ::= E
                prod1 = Production(Sort(ul.sort), Seq(NonTerminal(Sort(ul.childSort))));
                res.add(prod1);
            }

            parseProds.addAll(res);
            disambProds.addAll(res);
        }
        Module extensionM = new Module(mod.name() + "-EXTENSION", Set(mod), immutable(extensionProds), mod.att());
        Module disambM = new Module(mod.name() + "-DISAMB", Set(), immutable(disambProds), mod.att());
        Module parseM = new Module(mod.name() + "-PARSER", Set(), immutable(parseProds), mod.att());
        return new ParseInModule(mod, extensionM, disambM, parseM, this.strict);
    }

    private boolean isExceptionSort(Sort srt) {
        return kSorts.contains(srt) || srt.name().startsWith("#");
    }

    private Set<Sentence> makeCasts(Sort outerSort, Sort innerSort, Sort castSort) {
        Set<Sentence> prods = new HashSet<>();
        Att attrs1 = Att().add(Attribute.SORT_KEY, castSort.name());
        prods.add(Production("#SyntacticCast", castSort, Seq(NonTerminal(castSort), Terminal("::" + castSort.name())), attrs1));
        prods.add(Production("#SemanticCastTo" + castSort.name(),  castSort, Seq(NonTerminal(castSort), Terminal(":"  + castSort.name())), attrs1));
        prods.add(Production("#InnerCast",     outerSort, Seq(Terminal("{"), NonTerminal(castSort), Terminal("}"), Terminal("<:" + castSort.name())), attrs1));
        prods.add(Production("#OuterCast",     castSort, Seq(Terminal("{"), NonTerminal(innerSort), Terminal("}"), Terminal(":>" + castSort.name())), attrs1));
        return prods;
    }
}

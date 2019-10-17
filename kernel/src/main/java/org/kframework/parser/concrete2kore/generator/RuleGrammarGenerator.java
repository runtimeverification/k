// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.generator;

import org.apache.commons.collections4.trie.PatriciaTrie;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.GenerateSortPredicateSyntax;
import org.kframework.compile.GenerateSortProjections;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Sentence;
import org.kframework.definition.SortSynonym;
import org.kframework.definition.Terminal;
import org.kframework.definition.UserList;
import org.kframework.kil.loader.Constants;
import org.kframework.kore.Sort;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.StringUtil;
import scala.collection.Seq;
import scala.Option;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

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
    private static final Set<Sort> kSorts = new HashSet<>();

    static {
        kSorts.add(Sorts.KBott());
        kSorts.add(Sorts.K());
        kSorts.add(Sorts.KLabel());
        kSorts.add(Sorts.KList());
        kSorts.add(Sorts.KItem());
        kSorts.add(Sorts.KConfigVar());
        kSorts.add(Sorts.KString());
    }

    private static Set<Sort> kSorts() {
        return java.util.Collections.unmodifiableSet(kSorts);
    }
    /// modules that have a meaning:
    public static final String DEFAULT_LAYOUT = "DEFAULT-LAYOUT";
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
    public static final String RECORD_PRODS = "RECORD-PRODUCTIONS";

    public static final String POSTFIX = "-PROGRAM-PARSING";

    public static final String ID = "ID";
    public static final String ID_PROGRAM_PARSING = ID + POSTFIX;
    private static final String ID_SYNTAX = "ID$SYNTAX";
    private static final String ID_PROGRAM_PARSING_SYNTAX = "ID-PROGRAM-PARSING$SYNTAX";

    /**
     * Initialize a grammar generator.
     * @param baseK A Definition containing a K module giving the syntax of K itself.
     *              The default K syntax is defined in include/kast.k.
     */
    public RuleGrammarGenerator(Definition baseK) {
        this.baseK = baseK;
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
        Module newM = new Module( mod.name() + "-" + RULE_CELLS
                                , Set(mod, baseK.getModule(K).get(), baseK.getModule(RULE_CELLS).get(), baseK.getModule(DEFAULT_LAYOUT).get())
                                , Set()
                                , Att()
                                );
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
        Module newM = new Module( mod.name() + "-" + CONFIG_CELLS
                                , Set(mod, baseK.getModule(K).get(), baseK.getModule(CONFIG_CELLS).get(), baseK.getModule(DEFAULT_LAYOUT).get())
                                , Set()
                                , Att()
                                );
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
            Module newMod = ModuleTransformer.from(oldMod -> {
                Set<Module> imports = stream(oldMod.imports()).map(_import -> {
                    if (_import.name().endsWith("$SYNTAX")) {
                        Option<Module> programParsing = baseK.getModule(_import.name().substring(0, _import.name().length()-"$SYNTAX".length()) + "-PROGRAM-PARSING$SYNTAX");
                        if (programParsing.isDefined()) {
                            return programParsing.get();
                        }
                        return _import;
                    } else {
                        Option<Module> programParsing = baseK.getModule(_import.name() + "-PROGRAM-PARSING");
                        if (programParsing.isDefined()) {
                            return programParsing.get();
                        }
                        return _import;
                    }
                }).collect(Collectors.toSet());
                return Module.apply(oldMod.name(), immutable(imports), oldMod.localSentences(), oldMod.att());
            }, "apply program parsing modules").apply(mod);

            Set<Module> modules = new HashSet<Module>();
            modules.add(newMod);

            // import PROGRAM-LISTS so user lists are modified to parse programs
            modules.add(baseK.getModule(PROGRAM_LISTS).get());

            // check if `#Layout` has been declared, import `DEFAULT-LAYOUT` if not
            if (! mod.definedSorts().contains(Sorts.Layout())) {
                modules.add(baseK.getModule(DEFAULT_LAYOUT).get());
            }

            return Module.apply(mod.name() + "-PROGRAM-GRAMMAR", immutable(modules), Set(), Att());
        }
    }

    public static boolean isParserSort(Sort s) {
        return kSorts.contains(s) || s.name().startsWith("#");
    }

    /* use this overload if you don't need to profile rule parse times. */
    public static ParseInModule getCombinedGrammar(Module mod, boolean strict) {
      return getCombinedGrammar(mod, strict, false, null);
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
    public static ParseInModule getCombinedGrammar(Module mod, boolean strict, boolean timing, FileUtil files) {
        Set<Sentence> prods = new HashSet<>();
        Set<Sentence> extensionProds = new HashSet<>();
        Set<Sentence> disambProds;

        if (mod.importedModuleNames().contains(AUTO_CASTS)) { // create the diamond
            Set<Sentence> temp;
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!isParserSort(srt) || mod.subsorts().directlyLessThan(Sorts.KVariable(), srt)) {
                    // K ::= K "::Sort" | K ":Sort" | K "<:Sort" | K ":>Sort"
                    prods.addAll(makeCasts(Sorts.KBott(), Sorts.K(), srt, srt));
                }
            }
            prods.addAll(makeCasts(Sorts.KLabel(), Sorts.KLabel(), Sorts.KLabel(), Sorts.KLabel()));
            prods.addAll(makeCasts(Sorts.KList(), Sorts.KList(), Sorts.KList(), Sorts.KList()));
            prods.addAll(makeCasts(Sorts.KBott(), Sorts.K(), Sorts.KItem(), Sorts.KItem()));
            prods.addAll(makeCasts(Sorts.KBott(), Sorts.K(), Sorts.K(), Sorts.K()));
            for (SortSynonym syn : iterable(mod.sortSynonyms())) {
                prods.addAll(makeCasts(Sorts.KBott(), Sorts.K(), syn.newSort(), syn.oldSort()));
            }
        }

        if (mod.importedModuleNames().contains(RECORD_PRODS)) {
            for (Production p : iterable(mod.productions())) {
                if (p.isPrefixProduction()) {
                    prods.addAll(mutable(p.recordProductions()));
                }
            }
        }

        for (Sort s : iterable(mod.definedSorts())) {
            prods.addAll(new GenerateSortPredicateSyntax().gen(mod, s));
            prods.addAll(new GenerateSortProjections(mod).gen(s).collect(Collectors.toSet()));
        }

        for (Production p : iterable(mod.productions())) {
            prods.addAll(new GenerateSortProjections(mod).gen(p).collect(Collectors.toSet()));
            if (p.params().nonEmpty()) {
                Sort param = null;
                if (p.isSyntacticSubsort() && p.params().size() == 1) {
                    param = p.params().apply(0);
                } else {
                    // we don't actually need to emit a parameter except in the case of the return sort
                    // because the type checker will never actually reject a parse because the sorts in
                    // the arguments don't match; it will simply infer sort K for those arguments.
                    param = p.isSortVariable(p.sort()) ? p.sort() : null;
                }
                List<List<Sort>> sortTuples = makeAllSortTuples(param == null ? 0 : 1, mod);
                for (List<Sort> tuple : sortTuples) {
                    assert(tuple.size() < 2);
                    Sort returnSort = p.sort();
                    if (returnSort.equals(param)) {
                        returnSort = tuple.get(0);
                    }
                    List<ProductionItem> pis = new ArrayList<>();
                    pis.addAll(mutable(p.items()));
                    Map<Sort, Sort> subst;
                    if (param == null) {
                        subst = Collections.emptyMap();
                    } else {
                        subst = Collections.singletonMap(param, tuple.get(0));
                    }
                    for (int i = 0; i < pis.size(); i++) {
                        ProductionItem pi = pis.get(i);
                        if (pi instanceof NonTerminal) {
                            Sort s = ((NonTerminal)pi).sort();
                            if (p.isSortVariable(s)) {
                              pis.set(i, NonTerminal(subst.getOrDefault(s, Sorts.K()), ((NonTerminal)pi).name()));
                            }
                        }
                    }
                    if (p.isSyntacticSubsort() && mod.subsorts().lessThanEq(returnSort, ((NonTerminal)pis.get(0)).sort())) {
                        continue;
                    }
                    prods.add(Production(p.klabel().map(lbl -> KLabel(lbl.name())), Seq(), returnSort, immutable(pis), p.att().add(Constants.ORIGINAL_PRD, Production.class, p)));
                }
            }
        }
        extensionProds.addAll(prods);

        boolean addRuleCells;
        if (mod.importedModuleNames().contains(RULE_CELLS)) { // prepare cell productions for rule parsing
            // make sure a configuration actually exists, otherwise ConfigurationInfoFromModule explodes.
            addRuleCells = mod.sentences().exists(p -> p instanceof Production && ((Production) p).att().contains("cell"));
        } else {
            addRuleCells = false;
        }
        boolean addConfigCells = mod.importedModuleNames().contains(CONFIG_CELLS);
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
                        body = NonTerminal(Sorts.Bag());
                    }
                    final ProductionItem optDots = NonTerminal(Sort("#OptionalDots"));
                    Seq<ProductionItem> pi = Seq(p.items().head(), optDots, body, optDots, p.items().last());
                    Production p1 = Production(p.klabel().get(), p.sort(), pi, p.att());
                    Production p2 = Production(Seq(), Sorts.Cell(), Seq(NonTerminal(p.sort())));
                    return Stream.of(p1, p2);
                }
                if (s instanceof Production && (s.att().contains("cellFragment", Sort.class))) {
                    Production p = (Production) s;
                    Production p1 = Production(Seq(), Sorts.Cell(), Seq(NonTerminal(p.sort())));
                    return Stream.of(p, p1);
                }
                return Stream.of(s);
            }).collect(Collectors.toSet());
        } else if (addConfigCells) {
            // remove cells from parsing config cells so they don't conflict with the production in kast.k
            // also add all matching terminals to the #CellName sort
            for (Sentence prod : extensionProds) {
              if (prod instanceof Production) {
                for (ProductionItem pi : iterable(((Production)prod).items())) {
                  if (pi instanceof Terminal) {
                    Terminal t = (Terminal)pi;
                    if (t.value().matches("[A-Za-z][A-Za-z0-9\\-]*")) {
                      prods.add(Production(Seq(), Sorts.CellName(), Seq(t), Att().add("token")));
                    }
                  }
                }
              }
            }
            parseProds = Stream.concat(prods.stream(), stream(mod.sentences()).filter(s -> !s.att().contains("cell"))).collect(Collectors.toSet());
        } else
            parseProds = Stream.concat(prods.stream(), stream(mod.sentences())).collect(Collectors.toSet());

        if (mod.importedModuleNames().contains(AUTO_FOLLOW)) {
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
                        p = Production(p.klabel().get(), p.sort(), p.items(), p.att());
                    else
                        p = Production(p.params(), p.sort(), p.items(), p.att());
                    return p;
                }
                return s;
            }).collect(Collectors.toSet());
        }

        disambProds = parseProds.stream().collect(Collectors.toSet());
        if (mod.importedModuleNames().contains(PROGRAM_LISTS)) {
            Set<Sentence> prods3 = new HashSet<>();
            // if no start symbol has been defined in the configuration, then use K
            for (Sort srt : iterable(mod.definedSorts())) {
                if (!isParserSort(srt) && !mod.listSorts().contains(srt)) {
                    // K ::= Sort
                    prods3.add(Production(Seq(), Sorts.K(), Seq(NonTerminal(srt)), Att()));
                }
            }
            // for each triple, generate a new pattern which works better for parsing lists in programs.
            prods3.addAll(parseProds.stream().collect(Collectors.toSet()));
            java.util.Set<Sentence> res = new HashSet<>();
            for (UserList ul : UserList.getLists(prods3)) {
                org.kframework.definition.Production prod1, prod2, prod3, prod4, prod5;

                Att newAtts = ul.attrs.remove("userList");
                // Es#Terminator ::= "" [klabel('.Es)]
                prod1 = Production(ul.terminatorKLabel, Sort(ul.sort.name() + "#Terminator", ul.sort.params()), Seq(Terminal("")),
                        newAtts.remove("format").add(Constants.ORIGINAL_PRD, Production.class, ul.pTerminator));
                // Ne#Es ::= E "," Ne#Es [klabel('_,_)]
                prod2 = Production(ul.klabel, Sort("Ne#" + ul.sort.name(), ul.sort.params()),
                        Seq(NonTerminal(ul.childSort), Terminal(ul.separator), NonTerminal(Sort("Ne#" + ul.sort.name(), ul.sort.params()))),
                        newAtts.add(Constants.ORIGINAL_PRD, Production.class, ul.pList));
                // Ne#Es ::= E "" Es#Terminator [klabel('_,_)]
                prod3 = Production(ul.klabel, Sort("Ne#" + ul.sort.name(), ul.sort.params()),
                        Seq(NonTerminal(ul.childSort), Terminal(""), NonTerminal(Sort(ul.sort.name() + "#Terminator", ul.sort.params()))),
                        newAtts.add(Constants.ORIGINAL_PRD, Production.class, ul.pList));
                // Es ::= Ne#Es
                prod4 = Production(Seq(), ul.sort, Seq(NonTerminal(Sort("Ne#" + ul.sort.name(), ul.sort.params()))));
                // Es ::= Es#Terminator // if the list is *
                prod5 = Production(Seq(), ul.sort, Seq(NonTerminal(Sort(ul.sort.name() + "#Terminator", ul.sort.params()))));

                res.add(prod1);
                res.add(prod2);
                res.add(prod3);
                res.add(prod4);
                res.add(SyntaxSort(Sort(ul.sort.name() + "#Terminator", ul.sort.params())));
                res.add(SyntaxSort(Sort("Ne#" + ul.sort.name(), ul.sort.params())));
                if (!ul.nonEmpty) {
                    res.add(prod5);
                }
            }
            res.addAll(prods3.stream().filter(p -> !(p instanceof Production && (p.att().contains(Att.generatedByListSubsorting()) || p.att().contains(Att.userList())))).collect(Collectors.toSet()));
            parseProds = res;
        }

        if (mod.importedModuleNames().contains(RULE_LISTS)) {
            java.util.Set<Sentence> res = new HashSet<>();
            for (UserList ul : UserList.getLists(parseProds)) {
                org.kframework.definition.Production prod1;
                // Es ::= E
                prod1 = Production(Seq(), ul.sort, Seq(NonTerminal(ul.childSort)));
                res.add(prod1);
            }

            parseProds.addAll(res);
            disambProds.addAll(res);
        }
        Module extensionM = new Module(mod.name() + "-EXTENSION", Set(mod), immutable(extensionProds), mod.att());
        Module disambM = new Module(mod.name() + "-DISAMB", Set(), immutable(disambProds), mod.att());
        Module parseM = new Module(mod.name() + "-PARSER", Set(), immutable(parseProds), mod.att());
        return new ParseInModule(mod, extensionM, disambM, parseM, strict, timing, files);
    }

    private static List<List<Sort>> makeAllSortTuples(int size, Module mod) {
        List<List<Sort>> res = new ArrayList<>();
        List<Sort> allSorts = stream(mod.definedSorts()).filter(s -> !isParserSort(s) || s.equals(Sorts.KItem()) || s.equals(Sorts.K())).collect(Collectors.toList());
        makeAllSortTuples(size, size, allSorts, res, new int[size]);
        return res;
    }

    private static void makeAllSortTuples(int level, int size, List<Sort> sorts, List<List<Sort>> res, int[] indices) {
        if (level == 0) {
            List<Sort> tuple = new ArrayList<>();
            for (int i = 0; i < indices.length; i++) {
                tuple.add(sorts.get(indices[i]));
            }
            res.add(tuple);
        } else {
            for (int i = 0; i < sorts.size(); i++) {
                indices[level-1] = i;
                makeAllSortTuples(level-1, size, sorts, res, indices);
            }
        }
    }

    private static Set<Sentence> makeCasts(Sort outerSort, Sort innerSort, Sort castSort, Sort labelSort) {
        Set<Sentence> prods = new HashSet<>();
        Att attrs1 = Att().add(Sort.class, castSort);
        prods.add(Production(KLabel("#SyntacticCast"), castSort, Seq(NonTerminal(labelSort), Terminal("::" + castSort.toString())), attrs1.add("format", "%1%2")));
        prods.add(Production(KLabel("#SemanticCastTo" + labelSort.name(), labelSort.params()), labelSort, Seq(NonTerminal(labelSort), Terminal(":"  + castSort.toString())), attrs1.add("format", "%1%2")));
        prods.add(Production(KLabel("#InnerCast"), outerSort, Seq(Terminal("{"), NonTerminal(labelSort), Terminal("}"), Terminal("<:" + castSort.toString())), attrs1.add("format", "%1 %2 %3%4")));
        prods.add(Production(KLabel("#OuterCast"), labelSort, Seq(Terminal("{"), NonTerminal(innerSort), Terminal("}"), Terminal(":>" + castSort.toString())), attrs1.add("format", "%1 %2 %3%4")));
        return prods;
    }
}

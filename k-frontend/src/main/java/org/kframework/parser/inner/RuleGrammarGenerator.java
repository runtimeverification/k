// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.definition.Constructors.Module;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.UnaryOperator;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.apache.commons.collections4.trie.PatriciaTrie;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.GenerateSortPredicateSyntax;
import org.kframework.compile.GenerateSortProjections;
import org.kframework.definition.Definition;
import org.kframework.definition.Import;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Sentence;
import org.kframework.definition.SortSynonym;
import org.kframework.definition.Terminal;
import org.kframework.definition.UidProvider;
import org.kframework.definition.UserList;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.parser.inner.kernel.Scanner;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.InnerParsingOptions;
import scala.Option;
import scala.Tuple3;

/**
 * Generator for rule and ground parsers. Takes as input a reference to a definition containing all
 * the base syntax of K and uses it to generate a grammar by connecting all users sorts in a lattice
 * with the top sort KItem#Top and the bottom sort KItem#Bottom.
 *
 * <p>The instances of the non-terminal KItem is renamed in KItem#Top if found in the right hand
 * side of a production, and into KItem#Bottom if found in the left hand side.
 */
public record RuleGrammarGenerator(Definition baseK) {

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

  /// modules that have a meaning:
  public static final String DEFAULT_LAYOUT = "DEFAULT-LAYOUT";
  public static final String RULE_CELLS = "RULE-CELLS";
  public static final String CONFIG_CELLS = "CONFIG-CELLS";
  public static final String K = "K";
  public static final String AUTO_CASTS = "AUTO-CASTS";
  public static final String AUTO_FOLLOW = "AUTO-FOLLOW";
  public static final String PROGRAM_LISTS = "PROGRAM-LISTS";
  public static final String RULE_LISTS = "RULE-LISTS";
  public static final String RECORD_PRODS = "RECORD-PRODUCTIONS";
  public static final String SORT_PREDICATES = "SORT-PREDICATES";

  public static final String POSTFIX = "-PROGRAM-PARSING";

  public static final String ID = "ID";
  private static final String ID_SYNTAX = "ID-SYNTAX";
  public static final String ID_PROGRAM_PARSING = ID_SYNTAX + POSTFIX;

  /**
   * Initialize a grammar generator.
   *
   * @param baseK A Definition containing a K module giving the syntax of K itself. The default K
   *     syntax is defined in include/kast.k.
   */
  public RuleGrammarGenerator {}

  /**
   * Creates the seed module that can be used to parse rules. Imports module markers RULE-CELLS and
   * K found in /include/kast.k.
   *
   * @param mod The user defined module from which to start.
   * @return a new module which imports the original user module and a set of marker modules.
   */
  public Module getRuleGrammar(Module mod) {
    return getGrammar(mod, RULE_CELLS);
  }

  private Module getGrammar(Module mod, String name) {
    // import RULE-CELLS in order to parse cells specific to rules
    Module newM =
        new Module(
            mod.name() + "-" + name,
            mod.imports()
                .$bar(
                    Set(
                        Import(baseK.getModule(K).get(), true),
                        Import(baseK.getModule(name).get(), true),
                        Import(baseK.getModule(DEFAULT_LAYOUT).get(), true)))
                .toSet(),
            mod.localSentences(),
            mod.att());
    return newM;
  }

  /**
   * Creates the seed module that can be used to parse configurations. Imports module markers
   * CONFIG-CELLS and K found in /include/kast.k.
   *
   * @param mod The user defined module from which to start.
   * @return a new module which imports the original user module and a set of marker modules.
   */
  public Module getConfigGrammar(Module mod) {
    return getGrammar(mod, CONFIG_CELLS);
  }

  /**
   * Creates the seed module that can be used to parse programs. Imports module markers
   * PROGRAM-LISTS found in /include/kast.k.
   *
   * @param mod The user defined module from which to start.
   * @return a new module which imports the original user module and a set of marker modules.
   */
  public Module getProgramsGrammar(Module mod) {

    if (mod.name().endsWith(POSTFIX)) {
      return mod;
    } else {
      Module newMod =
          ModuleTransformer.from(
                  oldMod -> {
                    UnaryOperator<Import> f =
                        _import -> {
                          Option<Module> programParsing =
                              baseK.getModule(_import.module().name() + "-PROGRAM-PARSING");
                          if (programParsing.isDefined()) {
                            return Import(programParsing.get(), _import.isPublic());
                          }
                          return _import;
                        };
                    Set<Import> imports =
                        stream(oldMod.imports()).map(f).collect(Collectors.toSet());
                    return Module.apply(
                        oldMod.name(), immutable(imports), oldMod.localSentences(), oldMod.att());
                  },
                  "apply program parsing modules")
              .apply(mod);

      Set<Import> modules = new HashSet<Import>();
      for (Import m : iterable(newMod.imports())) {
        modules.add(m);
      }

      // import PROGRAM-LISTS so user lists are modified to parse programs
      modules.add(Import(baseK.getModule(PROGRAM_LISTS).get(), true));

      // check if `#Layout` has been declared, import `DEFAULT-LAYOUT` if not
      if (!mod.allSorts().contains(Sorts.Layout())) {
        modules.add(Import(baseK.getModule(DEFAULT_LAYOUT).get(), true));
      }

      return Module.apply(
          mod.name() + "-PROGRAM-GRAMMAR",
          immutable(modules),
          newMod.localSentences(),
          newMod.att());
    }
  }

  public static boolean isParserSort(Sort s) {
    return kSorts.contains(s) || s.name().startsWith("#") || s.isNat();
  }

  /* use this overload if you don't need to profile rule parse times. */
  public static ParseInModule getCombinedGrammar(Module mod, FileUtil files) {
    return getCombinedGrammar(
        mod,
        false,
        false,
        false,
        files,
        null,
        InnerParsingOptions.TypeInferenceMode.DEFAULT,
        false);
  }

  public static ParseInModule getCombinedGrammar(
      Module mod, FileUtil files, boolean partialParseDebug) {
    return getCombinedGrammar(
        mod,
        false,
        false,
        false,
        files,
        null,
        InnerParsingOptions.TypeInferenceMode.DEFAULT,
        partialParseDebug);
  }

  public static ParseInModule getCombinedGrammar(Module mod, boolean timing, FileUtil files) {
    return getCombinedGrammar(
        mod,
        timing,
        false,
        false,
        files,
        null,
        InnerParsingOptions.TypeInferenceMode.DEFAULT,
        false);
  }

  public static ParseInModule getCombinedGrammar(
      Module mod,
      boolean timing,
      FileUtil files,
      String debugTypeInference,
      InnerParsingOptions.TypeInferenceMode typeInferenceMode) {
    return getCombinedGrammar(
        mod, timing, false, false, files, debugTypeInference, typeInferenceMode, false);
  }

  public static ParseInModule getCombinedGrammar(
      Module mod, boolean timing, boolean isBison, FileUtil files) {
    return getCombinedGrammar(
        mod,
        timing,
        isBison,
        false,
        files,
        null,
        InnerParsingOptions.TypeInferenceMode.DEFAULT,
        false);
  }

  public static ParseInModule getCombinedGrammar(
      Module mod, boolean timing, boolean isBison, boolean forGlobalScanner, FileUtil files) {
    return getCombinedGrammar(
        mod,
        timing,
        isBison,
        forGlobalScanner,
        files,
        null,
        InnerParsingOptions.TypeInferenceMode.DEFAULT,
        false);
  }

  public static ParseInModule getCombinedGrammar(
      Module mod, Scanner scanner, boolean timing, boolean isBison, FileUtil files) {
    return getCombinedGrammar(
        mod,
        scanner,
        timing,
        isBison,
        files,
        null,
        InnerParsingOptions.TypeInferenceMode.DEFAULT,
        false);
  }

  // the forGlobalScanner flag tells the ParseInModule class not to exclude
  // private syntax from the grammar generated for the module. It should
  // not be used when actually performing parsing as this will lead to
  // incorrect grammars. However, it is used in one place in the code:
  // during rule parsing, we generate a single scanner to scan all the
  // modules. This must include the private syntax of those modules,
  // otherwise we would not be able to use it to scan the modules in which
  //  that private syntax is visible.

  /**
   * Create the rule parser for the given module. It creates a module which includes the given
   * module and the base K module given to the constructor. The new module contains syntax
   * declaration for Casts and the diamond which connects the user concrete syntax with K syntax.
   *
   * @param mod module for which to create the parser.
   * @param partialParseDebug
   * @return parser which applies disambiguation filters by default.
   */
  public static ParseInModule getCombinedGrammar(
      Module mod,
      boolean timing,
      boolean isBison,
      boolean forGlobalScanner,
      FileUtil files,
      String debugTypeInference,
      InnerParsingOptions.TypeInferenceMode typeInferenceMode,
      boolean partialParseDebug) {
    return new ParseInModule(
        mod,
        timing,
        isBison,
        forGlobalScanner,
        files,
        debugTypeInference,
        typeInferenceMode,
        partialParseDebug);
  }

  public static ParseInModule getCombinedGrammar(
      Module mod,
      Scanner scanner,
      boolean timing,
      boolean isBison,
      FileUtil files,
      String debugTypeInference,
      InnerParsingOptions.TypeInferenceMode typeInferenceMode,
      boolean partialParseDebug) {
    return new ParseInModule(
        mod,
        scanner,
        timing,
        isBison,
        false,
        files,
        debugTypeInference,
        typeInferenceMode,
        partialParseDebug);
  }

  /**
   * Generate the derived extension, disambiguation and parsing modules from a user module.
   *
   * <p>When performing different parts of the compilation pipeline, we need to use derived modules
   * with different properties to the user-supplied source module. This method adds additional
   * syntax to the user module to do so.
   *
   * <p>TODO: analysis of the properties of these modules: K Issue #1278
   *
   * @param mod The user module to transform.
   * @param isBison If true, modules with the `not-lr1` attribute will be dropped.
   * @param forGlobalScanner If false, only the public signature of the user module is considered
   *     (i.e. private imports are dropped).
   * @param subsortUserLists If true, a subsorting production `Es ::= E` is added to the
   *     disambiguation module for each user list sort `Es`.
   * @return A tuple `(extension, disambiguation, parsing)` of derived modules.
   */
  public static Tuple3<Module, Module, Module> getCombinedGrammarImpl(
      Module mod, boolean isBison, boolean forGlobalScanner, boolean subsortUserLists) {
    Set<Sentence> prods = new HashSet<>();
    Set<Sentence> extensionProds = new HashSet<>();
    Set<Sentence> disambProds;

    Module origMod = mod;

    if (!forGlobalScanner) {
      mod = mod.signature();
    }

    if (isBison) {
      mod =
          ModuleTransformer.from(
                  m -> {
                    if (m.att().contains(Att.NOT_LR1())) {
                      return Module(m.name(), m.imports(), Set(), m.att());
                    }
                    return m;
                  },
                  "strip not-lr1 modules from bison grammar")
              .apply(mod);
    }

    if (mod.importedModuleNames().contains(AUTO_CASTS)) { // create the diamond
      for (Sort srt : iterable(mod.allSorts())) {
        if (!isParserSort(srt) || mod.subsorts().directlyLessThan(Sorts.KVariable(), srt)) {
          // K ::= K "::Sort" | K ":Sort" | K "<:Sort" | K ":>Sort"
          prods.addAll(makeCasts(Sorts.K(), srt, srt));
        }
      }
      prods.addAll(makeCasts(Sorts.KLabel(), Sorts.KLabel(), Sorts.KLabel()));
      prods.addAll(makeCasts(Sorts.KList(), Sorts.KList(), Sorts.KList()));
      prods.addAll(makeCasts(Sorts.K(), Sorts.KItem(), Sorts.KItem()));
      prods.addAll(makeCasts(Sorts.K(), Sorts.K(), Sorts.K()));
      for (SortSynonym syn : iterable(mod.sortSynonyms())) {
        prods.addAll(makeCasts(Sorts.K(), syn.newSort(), syn.oldSort()));
      }
    }

    if (mod.importedModuleNames().contains(SORT_PREDICATES)) {
      for (Sort s : iterable(mod.allSorts())) {
        prods.addAll(new GenerateSortPredicateSyntax().gen(mod, s));
        prods.addAll(new GenerateSortProjections(mod).gen(s).collect(Collectors.toSet()));
      }
    }

    for (Production p : iterable(mod.productions()))
      prods.addAll(new GenerateSortProjections(mod).gen(p).collect(Collectors.toSet()));

    // Because parametric productions introduce Non-Terminal names that do not exist in the module,
    // we can't
    // create a valid parsing grammar.
    // Here we go through every parametric production and, we replace it with concrete sorts.
    // We have 4 distinct cases depending on whether the return type of the production is parametric
    // or not:
    //   1 - prod sort is a simple parameter
    //   2 - prod sort is a parametric sort
    //   3 - special case for `syntax {Sort} KItem ::= Sort` // the subsort production found in
    // kast.md
    //   4 - prod sort is a concrete sort.
    // Because, at parse time, the prod sort is decided by the parent production we can instantiate
    // it with concrete
    // sorts. Parameters appearing only on the RHS of a production do not have any sort information
    // at parsing time,
    // so we use the top sort `K` as a placeholder. Meaning we can expect anything there. The
    // connection is then handled
    // at case 3 where we add subsorts for every parsable sort in the module.
    // TODO: for now we only have `MInt{Widht}` as parametric sorts, so we can treat it as a corner
    // case.
    // LHS gets instantiated the same way, but RHS gets instantiated with `MInt{K}` and we need to
    // add an extra subsort
    // production `syntax MInt{K} ::= MInt{6}` to make the connection between the new sort and the
    // concrete sorts.
    // This production doesn't have a klabel so it's not going to appear in the final AST.
    List<Sort> allSorts =
        stream(mod.allSorts())
            .filter(s -> (!isParserSort(s) || s.equals(Sorts.KItem()) || s.equals(Sorts.K())))
            .toList();
    for (Production p : iterable(mod.productions())) {
      if (p.params().nonEmpty()) {
        if (p.params().contains(p.sort())) { // case 1
          // syntax {P, R} P ::= P "+" R "-" Int
          // syntax        S ::= S "+" K "-" Int
          for (Sort s : allSorts) {
            List<Sort> instantiationMask = new ArrayList<>();
            for (Sort param : mutable(p.params()))
              if (param.equals(p.sort())) instantiationMask.add(s);
              else instantiationMask.add(Sorts.K());
            Production subst = p.substitute(immutable(instantiationMask));
            Production p1 =
                Production(
                    subst.klabel().map(lbl -> KLabel(lbl.name())),
                    Seq(),
                    subst.sort(),
                    subst.items(),
                    subst.att().add(Att.ORIGINAL_PRD(), Production.class, p));
            prods.add(p1);
          }
        } else if (!p.sort().params().isEmpty()) { // case 2
          // TODO: assuming sorts have only one parameter for now
          // syntax {W, X, Y} MInt{W} ::= MInt{W} "+" MInt{X} "-" Y "/" Int
          // syntax           MInt{6} ::= MInt{6} "+" MInt{K} "-" K "/" Int
          Set<Sort> instantations = mutable(mod.definedInstantiations().apply(p.sort().head()));
          for (Sort s : instantations) {
            List<Sort> instantiationMask = new ArrayList<>();
            for (Sort param : mutable(p.params()))
              if (param.equals(p.sort().params().apply(0)))
                instantiationMask.add(s.params().apply(0));
              else instantiationMask.add(Sorts.K());
            Production subst = p.substitute(immutable(instantiationMask));
            Production p1 =
                Production(
                    subst.klabel().map(lbl -> KLabel(lbl.name())),
                    Seq(),
                    subst.sort(),
                    subst.items(),
                    subst.att().add(Att.ORIGINAL_PRD(), Production.class, p));
            prods.add(p1);
          }
        } else if (p.isSyntacticSubsort()) { // case 3
          // a single production found in kast.md that handles the subsorting to the top sort
          // syntax {Sort} KItem ::= Sort
          // syntax        KItem ::= Int
          for (Sort s : allSorts) {
            if (!p.params().contains(p.sort()) && (s.equals(Sorts.KItem()) || s.equals(Sorts.K())))
              continue;
            List<Sort> instantiationMask = new ArrayList<>();
            instantiationMask.add(s);
            Production subst = p.substitute(immutable(instantiationMask));
            Production p1 =
                Production(
                    subst.klabel().map(lbl -> KLabel(lbl.name())),
                    Seq(),
                    subst.sort(),
                    subst.items(),
                    subst.att().add(Att.ORIGINAL_PRD(), Production.class, p));
            prods.add(p1);
          }
        } else { // case 4
          // the rest of the productions that return a concrete sort can accept any sort inside
          // syntax {P} Int ::= P "+" Int
          // syntax     Int ::= K "+" Int
          List<Sort> instantiationMask = new ArrayList<>();
          for (Sort ignored : mutable(p.params())) instantiationMask.add(Sorts.K());
          Production subst = p.substitute(immutable(instantiationMask));
          Production p1 =
              Production(
                  subst.klabel().map(lbl -> KLabel(lbl.name())),
                  Seq(),
                  subst.sort(),
                  subst.items(),
                  subst.att().add(Att.ORIGINAL_PRD(), Production.class, p));
          prods.add(p1);
        }
      }
    }
    extensionProds.addAll(prods);

    Set<Sentence> recordProds = new HashSet<>();
    if (mod.importedModuleNames().contains(RECORD_PRODS)) {
      // these should be visible only in the parsing module
      // but are required by config cell names
      UidProvider uid = new UidProvider(mod.name());
      for (Production p : iterable(mod.productions())) {
        if (p.isPrefixProduction()) {
          recordProds.addAll(mutable(p.recordProductions(uid)));
        }
      }
    }

    boolean addRuleCells;
    if (mod.importedModuleNames()
        .contains(RULE_CELLS)) { // prepare cell productions for rule parsing
      // make sure a configuration actually exists, otherwise ConfigurationInfoFromModule explodes.
      addRuleCells =
          mod.sentences().exists(p -> p instanceof Production && p.att().contains(Att.CELL()));
    } else {
      addRuleCells = false;
    }
    boolean addConfigCells = mod.importedModuleNames().contains(CONFIG_CELLS);
    Set<Sentence> parseProds;
    if (addRuleCells) {
      ConfigurationInfo cfgInfo = new ConfigurationInfoFromModule(mod);
      parseProds =
          Stream.concat(prods.stream(), stream(mod.sentences()))
              .flatMap(
                  s -> {
                    if (s instanceof Production p && (s.att().contains(Att.CELL()))) {
                      // assuming that productions tagged with 'cell' start and end with terminals,
                      // and only have non-terminals in the middle
                      assert p.items().head() instanceof Terminal
                          || p.items().head() instanceof RegexTerminal;
                      assert p.items().last() instanceof Terminal
                          || p.items().last() instanceof RegexTerminal;
                      final ProductionItem body;
                      if (cfgInfo.isLeafCell(p.sort())) {
                        body = p.items().apply(1);
                      } else {
                        body = NonTerminal(Sorts.Bag());
                      }
                      final ProductionItem optDots = NonTerminal(Sort("#OptionalDots"));
                      scala.collection.immutable.Seq<ProductionItem> pi =
                          Seq(p.items().head(), optDots, body, optDots, p.items().last());
                      Production p1 = Production(p.klabel().get(), p.sort(), pi, p.att());
                      Production p2 = Production(Seq(), Sorts.Cell(), Seq(NonTerminal(p.sort())));
                      return Stream.of(p1, p2);
                    }
                    if (s instanceof Production p
                        && (s.att().contains(Att.CELL_FRAGMENT(), Sort.class))) {
                      Production p1 = Production(Seq(), Sorts.Cell(), Seq(NonTerminal(p.sort())));
                      return Stream.of(p, p1);
                    }
                    return Stream.of(s);
                  })
              .collect(Collectors.toSet());
    } else if (addConfigCells) {
      // remove cells from parsing config cells so they don't conflict with the production in kast.k
      // also add all matching terminals to the #CellName sort
      for (Sentence prod : extensionProds) {
        addCellNameProd(prods, prod);
      }
      for (Sentence prod : recordProds) {
        addCellNameProd(prods, prod);
      }
      for (Sentence prod : iterable(mod.productions())) {
        addCellNameProd(prods, prod);
      }
      parseProds =
          Stream.concat(
                  prods.stream(),
                  stream(mod.sentences()).filter(s -> !s.att().contains(Att.CELL())))
              .collect(Collectors.toSet());
    } else
      parseProds =
          Stream.concat(prods.stream(), stream(mod.sentences())).collect(Collectors.toSet());

    if (mod.importedModuleNames().contains(AUTO_FOLLOW)) {
      Object PRESENT = new Object();
      PatriciaTrie<Object> terminals =
          new PatriciaTrie<>(); // collect all terminals so we can do automatic follow restriction
      // for prefix terminals
      parseProds.stream()
          .filter(sent -> sent instanceof Production)
          .forEach(
              p ->
                  stream(((Production) p).items())
                      .forEach(
                          i -> {
                            if (i instanceof Terminal)
                              terminals.put(((Terminal) i).value(), PRESENT);
                          }));
      parseProds =
          parseProds.stream()
              .map(
                  s -> {
                    if (s instanceof Production p) {
                      if (p.sort().name().startsWith("#"))
                        return p; // don't do anything for such productions since they are advanced
                      // features
                      // rewrite productions to contain follow restrictions for prefix terminals
                      // example _==_ and _==K_ can produce ambiguities. Rewrite the first into
                      // _(==(?![K])_
                      // this also takes care of casting and productions that have ":"
                      if (p.klabel().isDefined())
                        p = Production(p.klabel().get(), p.sort(), p.items(), p.att());
                      else p = Production(p.params(), p.sort(), p.items(), p.att());
                      return p;
                    }
                    return s;
                  })
              .collect(Collectors.toSet());
    }

    disambProds = new HashSet<>(parseProds);

    for (SortHead sh : mutable(mod.definedInstantiations()).keySet()) {
      for (Sort s : mutable(mod.definedInstantiations().apply(sh))) {
        // syntax MInt{K} ::= MInt{6}
        Production p1 =
            Production(
                Option.empty(), Seq(), Sort(s.name(), Sorts.K()), Seq(NonTerminal(s)), Att.empty());
        parseProds.add(p1);
      }
    }

    if (mod.importedModuleNames().contains(PROGRAM_LISTS)) {
      Set<Sentence> prods3 = new HashSet<>();
      // if no start symbol has been defined in the configuration, then use K
      for (Sort srt : iterable(mod.allSorts())) {
        if (!isParserSort(srt) && !mod.listSorts().contains(srt)) {
          // KItem ::= Sort
          prods3.add(Production(Seq(), Sorts.KItem(), Seq(NonTerminal(srt)), Att.empty()));
        }
      }
      // Add KItem subsorts to disambiguation for use by sort inference
      disambProds.addAll(prods3);
      // for each triple, generate a new pattern which works better for parsing lists in programs.
      prods3.addAll(new HashSet<>(parseProds));
      Set<Sentence> res = new HashSet<>();
      for (UserList ul : UserList.getLists(prods3)) {
        Production prod1, prod2, prod3 = null, prod4 = null, prod5 = null;

        Att newAtts = ul.attrs.remove(Att.USER_LIST());
        if (ul.leftAssoc && ul.nonEmpty) {
          prod1 =
              Production(
                  ul.klabel,
                  ul.sort,
                  Seq(NonTerminal(ul.sort), Terminal(ul.separator), NonTerminal(ul.childSort)),
                  newAtts.add(Att.ORIGINAL_PRD(), Production.class, ul.pList));
          prod2 =
              Production(
                  Seq(),
                  ul.sort,
                  Seq(NonTerminal(ul.childSort)),
                  newAtts
                      .add(Att.ORIGINAL_PRD(), Production.class, ul.pList)
                      .add(Att.USER_LIST(), ul.klabel.name())
                      .add(Att.USER_LIST_TERMINATOR(), ul.terminatorKLabel.name()));
          prod3 =
              Production(
                  ul.terminatorKLabel,
                  Sort(ul.sort.name() + "#Terminator", ul.sort.params()),
                  Seq(Terminal("")),
                  newAtts
                      .remove(Att.FORMAT())
                      .add(Att.ORIGINAL_PRD(), Production.class, ul.pTerminator));
        } else if (ul.leftAssoc) {
          throw KEMException.compilerError("Cannot use List with --bison-lists", ul.pList);
        } else {
          // Es#Terminator ::= "" [klabel('.Es)]
          prod1 =
              Production(
                  ul.terminatorKLabel,
                  Sort(ul.sort.name() + "#Terminator", ul.sort.params()),
                  Seq(Terminal("")),
                  newAtts
                      .remove(Att.FORMAT())
                      .add(Att.ORIGINAL_PRD(), Production.class, ul.pTerminator));
          // Ne#Es ::= E "," Ne#Es [klabel('_,_)]
          prod2 =
              Production(
                  ul.klabel,
                  Sort("Ne#" + ul.sort.name(), ul.sort.params()),
                  Seq(
                      NonTerminal(ul.childSort),
                      Terminal(ul.separator),
                      NonTerminal(Sort("Ne#" + ul.sort.name(), ul.sort.params()))),
                  newAtts.add(Att.ORIGINAL_PRD(), Production.class, ul.pList));
          // Ne#Es ::= E "" Es#Terminator [klabel('_,_)]
          prod3 =
              Production(
                  ul.klabel,
                  Sort("Ne#" + ul.sort.name(), ul.sort.params()),
                  Seq(
                      NonTerminal(ul.childSort),
                      Terminal(""),
                      NonTerminal(Sort(ul.sort.name() + "#Terminator", ul.sort.params()))),
                  newAtts.add(Att.ORIGINAL_PRD(), Production.class, ul.pList));
          // Es ::= Ne#Es
          prod4 =
              Production(
                  Seq(),
                  ul.sort,
                  Seq(NonTerminal(Sort("Ne#" + ul.sort.name(), ul.sort.params()))),
                  Att.empty().add(Att.NOT_INJECTION()));
          // Es ::= Es#Terminator // if the list is *
          prod5 =
              Production(
                  Seq(),
                  ul.sort,
                  Seq(NonTerminal(Sort(ul.sort.name() + "#Terminator", ul.sort.params()))),
                  Att.empty().add(Att.NOT_INJECTION()));
        }

        res.add(prod1);
        res.add(prod2);
        res.add(prod3);
        if (!ul.leftAssoc) {
          res.add(prod4);
          res.add(SyntaxSort(Seq(), Sort(ul.sort.name() + "#Terminator", ul.sort.params())));
          res.add(SyntaxSort(Seq(), Sort("Ne#" + ul.sort.name(), ul.sort.params())));
          if (!ul.nonEmpty) {
            res.add(prod5);
          }
        }
      }
      res.addAll(
          prods3.stream()
              .filter(p -> !(p instanceof Production && p.att().contains(Att.USER_LIST())))
              .collect(Collectors.toSet()));
      parseProds = res;
    }

    if (mod.importedModuleNames().contains(RULE_LISTS) || subsortUserLists) {
      Set<Sentence> res = new HashSet<>();
      for (UserList ul : UserList.getLists(parseProds)) {
        Production prod1;
        // Es ::= E
        prod1 = Production(Seq(), ul.sort, Seq(NonTerminal(ul.childSort)));
        res.add(prod1);
      }

      parseProds.addAll(res);
      disambProds.addAll(res);
    }

    parseProds.addAll(recordProds);
    Att att = mod.att();
    List<String> notLrModules =
        stream(mod.importedModules())
            .filter(m -> m.att().contains(Att.NOT_LR1()))
            .map(Module::name)
            .toList();
    if (!notLrModules.isEmpty()) {
      att = att.add(Att.NOT_LR1_MODULES(), notLrModules.toString());
    }
    Module extensionM =
        new Module(
            mod.name() + "-EXTENSION", Set(Import(origMod, true)), immutable(extensionProds), att);
    Module disambM = new Module(mod.name() + "-DISAMB", Set(), immutable(disambProds), att);
    Module parseM = new Module(mod.name() + "-PARSER", Set(), immutable(parseProds), att);
    parseM.subsorts();
    return Tuple3.apply(extensionM, disambM, parseM);
  }

  private static final Pattern alphaNum = Pattern.compile("[A-Za-z][A-Za-z0-9\\-]*");

  private static void addCellNameProd(Set<Sentence> prods, Sentence prod) {
    if (prod instanceof Production) {
      for (ProductionItem pi : iterable(((Production) prod).items())) {
        if (pi instanceof Terminal t) {
          if (alphaNum.matcher(t.value()).matches()) {
            prods.add(Production(Seq(), Sorts.CellName(), Seq(t), Att.empty().add(Att.TOKEN())));
          }
        }
      }
    }
  }

  private static Set<Sentence> makeCasts(Sort innerSort, Sort castSort, Sort labelSort) {
    Set<Sentence> prods = new HashSet<>();
    Att attrs1 = Att.empty().add(Att.SORT(), Sort.class, castSort);
    prods.add(
        Production(
            KLabel("#SyntacticCast"),
            castSort,
            Seq(NonTerminal(labelSort), Terminal("::" + castSort.toString())),
            attrs1.add(Att.FORMAT(), "%1%2")));
    prods.add(
        Production(
            KLabel("#SyntacticCastBraced"),
            castSort,
            Seq(Terminal("{"), NonTerminal(labelSort), Terminal("}"), Terminal("::" + castSort)),
            attrs1.add(Att.FORMAT(), "%1 %2 %3%4")));
    prods.add(
        Production(
            KLabel("#SemanticCastTo" + labelSort.toString()),
            labelSort,
            Seq(NonTerminal(labelSort), Terminal(":" + castSort)),
            attrs1.add(Att.FORMAT(), "%1%2")));
    prods.add(
        Production(
            KLabel("#OuterCast"),
            labelSort,
            Seq(Terminal("{"), NonTerminal(innerSort), Terminal("}"), Terminal(":>" + castSort)),
            attrs1.add(Att.FORMAT(), "%1 %2 %3%4")));
    return prods;
  }
}

// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo.Multiplicity;
import org.kframework.definition.Constructors;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.definition.SyntaxSort;
import org.kframework.kore.*;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import scala.Option;
import scala.Tuple2;
import scala.Tuple4;
import scala.collection.Set;

/** Created by dwightguth on 3/27/15. */
public class GenerateSentencesFromConfigDecl {

  /**
   * Takes a configuration declaration and returns the sentences that it desugars into.
   *
   * <p>Cells of multiplicity 1 desugar into an initializer production, an initializer rule, and a
   * cell production.
   *
   * <p>Cells of multiplicity * desugar into an initializer production, an initializer rule, a cell
   * production, and a bag sort to represent a bag of those cells.
   *
   * <p>Cells of multiplicity ? desugar into an initializer production, an initializer rule, a cell
   * production, and an empty production indicating the absence of that cell.
   *
   * <p>Cells with children additionally generate a *CellFragment sort with the same arity as the
   * cell production, but the arguments made optional by generating additional sorts.
   *
   * <p>Cells which have parents and are not multiplicity * generate a CellOpt sort which is a
   * supersort of the cell sort and has an additional production name like {@code <cell>-absent}.
   * (For a cell with multiplicitly ? this is necessary to distinguish a fragment that did capture
   * the state of the cell when it wasn't present, from a cell fragment that didn't even try to
   * capture the cell).
   *
   * <p>Currently the implementation does not handle initializer rules; we will address this
   * eventually.
   *
   * @param body The body of the configuration declaration.
   * @param ensures The ensures clause of the configuration declaration.
   * @param att The attributes of the configuration declaration.
   * @param m The module the configuration declaration exists in.
   * @return A set of sentences representing the configuration declaration.
   */
  public static Set<Sentence> gen(KExceptionManager kem, K body, K ensures, Att att, Module m) {
    return genInternal(kem, body, ensures, att, m)._1();
  }

  /**
   * Recurses over a cell and computes all the sentences corresponding to its children, and then
   * generates the sentences for itself.
   *
   * @param term The term to be processed. Can be either a cell, in which case it processes that
   *     cell, a list of cells, in which case it processes each of those cells, or a noncell, in
   *     which case its parent is treated as a leaf cell.
   * @param ensures The ensures clause from the configuration declaration. This is appended to the
   *     initializer of the top cell, but not any other cells. The algorithm assumes this will be
   *     null if and only if it is not the top cell of a configuration declaration.
   * @param cfgAtt The attributes of the configuration declaration. Appended to all cell productions
   *     generated.
   * @param m The module the configuration declaration is in. Used to get the sort of leaf cells.
   * @return A tuple of the sentences generated, a list of the sorts of the children of the cell,
   *     and the body of the initializer.
   */
  private static Tuple4<Set<Sentence>, List<Sort>, K, Boolean> genInternal(
      KExceptionManager kem, K term, K ensures, Att cfgAtt, Module m) {
    if (term instanceof KApply kapp) {
      if (kapp.klabel().name().equals("#configCell")) {
        // is a single cell
        if (kapp.klist().size() == 4) {
          K startLabel = kapp.klist().items().get(0);
          K endLabel = kapp.klist().items().get(3);
          if (startLabel.equals(endLabel)) {
            if (startLabel instanceof KToken label) {
              if (label.sort().equals(Sort("#CellName"))) {
                String cellName = label.s();
                Att cellProperties = getCellPropertiesAsAtt(kapp.klist().items().get(1), cellName);
                Multiplicity multiplicity =
                    convertStringMultiplicity(cellProperties.getOption(Att.MULTIPLICITY()), term);
                boolean isStream = cellProperties.getOption(Att.STREAM()).isDefined();

                K cellContents = kapp.klist().items().get(2);
                Att att = cfgAtt;
                if (kapp.att().contains(Att.LOCATION(), Location.class))
                  att =
                      cfgAtt.add(
                          Att.LOCATION(),
                          Location.class,
                          kapp.att().get(Att.LOCATION(), Location.class));
                Tuple4<Set<Sentence>, List<Sort>, K, Boolean> childResult =
                    genInternal(kem, cellContents, null, att, m);

                boolean isLeafCell = childResult._4();
                Tuple4<Set<Sentence>, Sort, K, Boolean> myResult =
                    computeSentencesOfWellFormedCell(
                        kem,
                        isLeafCell,
                        isStream,
                        multiplicity,
                        att,
                        m,
                        cellName,
                        cellProperties,
                        childResult._2(),
                        childResult._3(),
                        ensures,
                        hasConfigOrRegularVariable(cellContents, m));
                return Tuple4.apply(
                    (Set<Sentence>) childResult._1().$bar(myResult._1()),
                    Lists.newArrayList(myResult._2()),
                    myResult._3(),
                    false);
              }
            }
          }
        }
        throw KEMException.compilerError("Malformed cell in configuration declaration.", term);
      } else if (kapp.klabel().name().equals("#externalCell")) {
        if (kapp.klist().size() == 1) {
          K startLabel = kapp.klist().items().get(0);
          if (startLabel instanceof KToken label) {
            if (label.sort().equals(Sort("#CellName"))) {
              String cellName = label.s();
              Sort sort = Sort(getSortOfCell(cellName));
              Option<scala.collection.immutable.Set<Production>> initializerProduction =
                  m.productionsFor().get(KLabel(getInitLabel(sort)));
              if (initializerProduction.isDefined()) {
                Set<Production> realProds =
                    stream(initializerProduction.get())
                        .filter(p -> !p.att().contains(Att.RECORD_PRD(), Production.class))
                        .collect(Collections.toSet());
                if (realProds.size() == 1) { // should be only a single initializer
                  if (realProds.head().items().size() == 1) {
                    // XCell ::= "initXCell"
                    return Tuple4.apply(
                        Set(), Lists.newArrayList(sort), KApply(KLabel(getInitLabel(sort))), true);
                  } else if (realProds.head().items().size() == 4) {
                    // XCell ::= "initXCell" "(" Map ")"
                    return Tuple4.apply(
                        Set(),
                        Lists.newArrayList(sort),
                        KApply(KLabel(getInitLabel(sort)), INIT),
                        true);
                  }
                }
              }
            }
          }
        }
        throw KEMException.compilerError(
            "Malformed external cell in configuration declaration.", term);
      } else if (KLabels.CELLS.equals(kapp.klabel())) {
        // is a cell bag, and thus represents the multiple children of its parent cell
        if (ensures != null) {
          // top level cell, therefore, should be the children of the generatedTop cell
          KToken cellLabel = KToken(KLabels.GENERATED_TOP_CELL_NAME, Sort("#CellName"));
          K generatedTop =
              KApply(
                  KLabel("#configCell"),
                  cellLabel,
                  KApply(KLabel("#cellPropertyListTerminator")),
                  term,
                  cellLabel);
          return genInternal(kem, generatedTop, ensures, cfgAtt, m);
        }
        List<K> cells = Assoc.flatten(kapp.klabel(), kapp.klist().items(), m);
        Set<Sentence> accumSentences = Set();
        List<Sort> sorts = Lists.newArrayList();
        List<K> initializers = Lists.newArrayList();
        for (K cell : cells) {
          // for each cell, generate the child and inform the parent of the children it contains
          Tuple4<Set<Sentence>, List<Sort>, K, Boolean> childResult =
              genInternal(kem, cell, null, cfgAtt, m);
          accumSentences = (Set<Sentence>) accumSentences.$bar(childResult._1());
          sorts.addAll(childResult._2());
          initializers.add(childResult._3());
        }
        return Tuple4.apply(
            accumSentences, sorts, KApply(KLabels.CELLS, immutable(initializers)), false);
      }
      // TODO: call generic getSort method of some kind
      // child of a leaf cell. Generate no productions, but inform parent that it has a child of a
      // particular sort.
      // A leaf cell initializes to the value specified in the configuration declaration.
      Sort sort = kapp.att().get(Att.PRODUCTION(), Production.class).sort();
      Tuple2<K, Set<Sentence>> res = getLeafInitializer(term);
      return Tuple4.apply(res._2(), Lists.newArrayList(sort), res._1(), true);
    } else if (term instanceof KToken ktoken) {
      // child of a leaf cell. Generate no productions, but inform parent that it has a child of a
      // particular sort.
      // A leaf cell initializes to the value specified in the configuration declaration.
      Tuple2<K, Set<Sentence>> res = getLeafInitializer(term);
      return Tuple4.apply(res._2(), Lists.newArrayList(ktoken.sort()), res._1(), true);
    } else if (term instanceof KSequence
        || term instanceof KVariable
        || term instanceof InjectedKLabel) {
      // child of a leaf cell. Generate no productions, but inform parent that it has a child of a
      // particular sort.
      // A leaf cell initializes to the value specified in the configuration declaration.
      Tuple2<K, Set<Sentence>> res = getLeafInitializer(term);
      return Tuple4.apply(res._2(), Lists.newArrayList(Sorts.K()), res._1(), true);
    } else {
      throw KEMException.compilerError(
          "Unexpected value found in configuration declaration, expected KToken, KSequence, or"
              + " KApply",
          term);
    }
  }

  public static String getInitLabel(Sort sort) {
    return "init" + sort.toString();
  }

  /**
   * Returns true if the specified term has a configuration or regular variable
   *
   * @param contents
   */
  private static boolean hasConfigOrRegularVariable(K contents, Module m) {
    FindConfigOrRegularVar visitor = new FindConfigOrRegularVar(m);
    visitor.apply(contents);
    return visitor.hasConfigVar;
  }

  private static class FindConfigOrRegularVar extends VisitK {

    private final Module m;
    boolean hasConfigVar;

    public FindConfigOrRegularVar(Module m) {
      this.m = m;
    }

    @Override
    public void apply(KToken k) {
      if (k.sort().equals(Sorts.KConfigVar())) {
        hasConfigVar = true;
      }
    }

    @Override
    public void apply(KApply kapp) {
      if (kapp.klabel().name().equals("#externalCell")) {
        if (kapp.klist().size() == 1) {
          K startLabel = kapp.klist().items().get(0);
          if (startLabel instanceof KToken label) {
            if (label.sort().equals(Sort("#CellName"))) {
              String cellName = label.s();
              Sort sort = Sort(getSortOfCell(cellName));
              Option<scala.collection.immutable.Set<Production>> initializerProduction =
                  m.productionsFor().get(KLabel(getInitLabel(sort)));
              if (initializerProduction.isDefined()) {
                Set<Production> realProds =
                    stream(initializerProduction.get())
                        .filter(p -> !p.att().contains(Att.RECORD_PRD(), Production.class))
                        .collect(Collections.toSet());
                if (realProds.size() == 1) { // should be only a single initializer
                  if (realProds.head().items().size() == 4) {
                    hasConfigVar = true;
                  }
                }
              }
            }
          }
        }
      }
      super.apply(kapp);
    }

    @Override
    public void apply(KVariable k) {
      hasConfigVar = true;
    }
  }

  /**
   * Returns the body of an initializer for a leaf cell: replaces any configuration variables with
   * map lookups in the initialization map.
   *
   * @param leafContents
   * @return
   */
  private static Tuple2<K, Set<Sentence>> getLeafInitializer(K leafContents) {
    class Holder {
      Set<Sentence> sentences = Set();
    }
    Holder h = new Holder();
    return Tuple2.apply(
        new TransformK() {
          private Sort sort;

          @Override
          public K apply(KApply k) {
            if (k.klabel().name().startsWith("#SemanticCastTo")) {
              sort = k.att().get(Att.PRODUCTION(), Production.class).sort();
            }
            return super.apply(k);
          }

          @Override
          public K apply(KToken k) {
            if (k.sort().equals(Sorts.KConfigVar())) {
              if (sort == null || sort.equals(Sorts.K())) {
                return KApply(
                    GenerateSortProjections.getProjectLbl(Sorts.KItem()),
                    KApply(KLabel("Map:lookup"), INIT, k));
              } else {
                return KApply(
                    GenerateSortProjections.getProjectLbl(sort),
                    KApply(KLabel("Map:lookup"), INIT, k));
              }
            }
            return k;
          }
        }.apply(leafContents),
        h.sentences);
  }

  private static final KVariable INIT =
      KVariable("Init", Att.empty().add(Att.SORT(), Sort.class, Sorts.Map()));

  /**
   * Generates the sentences associated with a particular cell.
   *
   * <p>As a special case, cells with the maincell attribute (usually just the {@code <k>} cell) are
   * generated with contents of sort K, rather than a narrower sort calculated from the contents.
   *
   * @param isLeaf true if this cell has no child cells.
   * @param isStream true if this cell has a stream attribute.
   * @param multiplicity The multiplicity of the cell
   * @param configAtt The attributes on the configuration declaration.
   * @param m The module containing the configuration.
   * @param cellName The name of the cell being generated.
   * @param cellProperties The attributes on the configuration cell (&lt;cell
   *     foo="bar"&gt;&lt;/cell&gt;
   * @param childSorts The list of sorts computed via recursion of the children of the current cell.
   * @param childInitializer The contents of the cell being processed, converted into the right hand
   *     side of an initializer.
   * @param ensures The ensures clause to be used; null if the cell is not a top cell.
   * @param hasConfigurationOrRegularVariable true if the initializer for the cell requires a
   *     configuration variable or a regular variable (when refering directly to configuration
   *     initializers). This causes cells of multiplicity * or ? to be initialized to a non-empty
   *     bag, and the initializer to take a Map argument containing the values of the configuration
   *     variables.
   * @return A tuple containing the sentences associated with the cell, the sort of the cell, and
   *     the term to be used to initialize this cell in the initializer of its parent cell.
   */
  private static Tuple4<Set<Sentence>, Sort, K, Boolean> computeSentencesOfWellFormedCell(
      KExceptionManager kem,
      boolean isLeaf,
      boolean isStream,
      Multiplicity multiplicity,
      Att configAtt,
      Module m,
      String cellName,
      Att cellProperties,
      List<Sort> childSorts,
      K childInitializer,
      K ensures,
      boolean hasConfigurationOrRegularVariable) {
    String sortName = getSortOfCell(cellName);
    Sort sort = Sort(sortName);

    if (cellProperties.contains(Att.MAINCELL())) {
      assert isLeaf;
      assert childSorts.size() == 1;
      childSorts = Lists.newArrayList(Sorts.K());
    }

    List<ProductionItem> items =
        Stream.concat(
                Stream.concat(
                    Stream.of(Terminal("<" + cellName + ">")),
                    childSorts.stream().map(Constructors::NonTerminal)),
                Stream.of(Terminal("</" + cellName + ">")))
            .collect(Collectors.toList());

    java.util.Set<Sentence> sentences = new HashSet<Sentence>();

    String klabel = "<" + cellName + ">";
    Att att = cellProperties.addAll(configAtt);

    StringBuilder format = new StringBuilder();
    if (!cellProperties.contains(Att.FORMAT())) {
      format.append("%1%i");
      int i;
      for (i = 2; i < 2 + childSorts.size(); i++) {
        format.append("%n%").append(i);
      }
      format.append("%d%n%").append(i);
      att = att.add(Att.FORMAT(), format.toString());
    }

    // syntax Cell ::= "<cell>" Children... "</cell>" [cell, cellProperties, configDeclAttributes]
    if (!m.definedKLabels().contains(KLabel(klabel)) && multiplicity != Multiplicity.OPTIONAL) {
      Production cellProduction = Production(KLabel(klabel), sort, immutable(items), att);
      sentences.add(cellProduction);
    }

    // syntax Cell ::= "initCell" [initializer, function]
    // -or-
    // syntax Cell ::= initCell(Map) [initializer, function]
    String initLabel = getInitLabel(sort);
    Sentence initializer;
    Rule initializerRule;
    Sort initSort = sort;

    if (multiplicity == Multiplicity.STAR) {
      String type = cellProperties.getOptional(Att.TYPE()).orElse("Bag");
      initSort = Sort(sortName + type);
    }

    if (hasConfigurationOrRegularVariable || isStream) {
      initializer =
          Production(
              KLabel(initLabel),
              initSort,
              Seq(Terminal(initLabel), Terminal("("), NonTerminal(Sorts.Map()), Terminal(")")),
              Att.empty().add(Att.INITIALIZER()).add(Att.FUNCTION()));
      initializerRule =
          Rule(
              KRewrite(
                  KApply(KLabel(initLabel), INIT),
                  IncompleteCellUtils.make(
                      KLabel("<" + cellName + ">"), false, childInitializer, false)),
              BooleanUtils.TRUE,
              ensures == null ? BooleanUtils.TRUE : ensures,
              Att.empty().add(Att.INITIALIZER()));
    } else {
      initializer =
          Production(
              KLabel(initLabel),
              initSort,
              Seq(Terminal(initLabel)),
              Att.empty().add(Att.INITIALIZER()).add(Att.FUNCTION()).add(Att.TOTAL()));
      initializerRule =
          Rule(
              KRewrite(
                  KApply(KLabel(initLabel)),
                  IncompleteCellUtils.make(
                      KLabel("<" + cellName + ">"), false, childInitializer, false)),
              BooleanUtils.TRUE,
              ensures == null ? BooleanUtils.TRUE : ensures,
              Att.empty().add(Att.INITIALIZER()));
    }
    if (!m.definedKLabels().contains(KLabel(initLabel))) {
      sentences.add(initializer);
    }
    sentences.add(initializerRule);

    if (!isLeaf) {
      // syntax CellFragment ::= <cellName>-fragment Child1CellOpt Child2CellOpt ... ChildNCellOpt
      // </cellName>-fragment [cellFragment(Cell)]
      // syntax Child1CellOpt[cellFragmentOpt(Child1Cell)] ::= Child1Cell |
      // "noChild1Cell"[cellFragmentOptAbsent]
      // ...
      // syntax ChildNCellOpt[cellFragmentOpt(ChildNCell)] ::= ChildNCell |
      // "noChildNCell"[cellFragmentOptAbsent]

      // The "CellOpt" sorts are added for cells of multiplicitly other than * to allow representing
      // fragments
      // that didn't try to capture the corresponding cell, from a cell fragment variable written
      // next to
      // an explicit pattern for some cells.
      // We don't need to add those sorts for cells of multiplicitly *, because explicit patterns in
      // the
      // context of a cell fragment variable can never be sure to capture all copies of such a cell.
      Sort fragmentSort = Sort(sortName + "Fragment");
      List<ProductionItem> fragmentItems = new ArrayList<ProductionItem>(2 + childSorts.size());
      fragmentItems.add(Terminal("<" + cellName + ">-fragment"));
      for (Sort childSort : childSorts) {
        if (!childSort.name().endsWith("Cell")) {
          // child was a multiplicity * List/Bag/Set
          fragmentItems.add(NonTerminal(childSort));
        } else {
          Sort childOptSort = Sort(childSort.name() + "Opt", childSort.params());
          fragmentItems.add(NonTerminal(childOptSort));

          sentences.add(Production(Seq(), childOptSort, List(NonTerminal(childSort))));
          if (!m.definedKLabels().contains(KLabel("no" + childSort))) {
            sentences.add(
                Production(
                    KLabel("no" + childSort),
                    childOptSort,
                    List(Terminal("no" + childSort)),
                    Att.empty().add(Att.CELL_OPT_ABSENT(), Sort.class, childSort)));
          }
        }
      }
      fragmentItems.add(Terminal("</" + cellName + ">-fragment"));
      if (!m.definedKLabels().contains(KLabel("<" + cellName + ">-fragment"))) {
        sentences.add(
            Production(
                KLabel("<" + cellName + ">-fragment"),
                fragmentSort,
                immutable(fragmentItems),
                Att.empty().add(Att.CELL_FRAGMENT(), Sort.class, Sort(sortName))));
      }
    }

    Sort cellsSort;
    K rhs;
    if (multiplicity == Multiplicity.STAR) {
      // syntax CellBag [hook(BAG.Bag)]
      // syntax CellBag ::= Cell
      // syntax CellBag ::= ".CellBag" [hook(BAG.unit), function]
      // syntax CellBag ::= CellBagItem(Cell) [hook(BAG.element), function]
      // syntax CellBag  ::= CellBag CellBag [assoc, comm, unit(.CellBag), element(CellBagItem),
      // wrapElement(<cell>), hook(BAG.concat), avoid, function]
      // -or-
      // syntax CellSet [hook(SET.Set)]
      // syntax CellSet ::= Cell
      // syntax CellSet ::= ".CellSet" [hook(SET.unit), function]
      // syntax CellSet ::= CellSetItem(Cell) [hook(SET.element), function]
      // syntax CellSet ::= CellSet CellSet [assoc, comm, idem, unit(.CellSet),
      // element(CellSetItem), wrapElement(<cell>), hook(SET.concat), avoid, function]
      // -or-
      // syntax CellMap [hook(MAP.Map)]
      // syntax CellMap ::= Cell
      // syntax CellMap ::= ".CellMap" [hook(MAP.unit), function]
      // syntax CellMap ::= CellMapItem(KeyCell, Cell) [hook(MAP.element), function]
      // syntax CellMap ::= CellMap CellMap [assoc, comm, unit(.CellMap), element(CellMapItem),
      // wrapElement(<cell>), hook(MAP.concat), avoid, function]
      // -or-
      // syntax CellList [hook(LIST.List)]
      // syntax CellList ::= Cell
      // syntax CellList ::= ".CellList" [hook(LIST.unit), function]
      // syntax CellList ::= CellListItem(Cell) [hook(LIST.element), function]
      // syntax CellList ::= CellList CellList [assoc, unit(.CellList), element(CellListItem),
      // wrapElement(<cell>), hook(LIST.concat), avoid, function]
      String type = cellProperties.getOptional(Att.TYPE()).orElse("Bag");
      Sort bagSort = Sort(sortName + type);
      Att bagAtt =
          Att.empty()
              .add(Att.ASSOC(), "")
              .add(Att.CELL_COLLECTION())
              .add(Att.ELEMENT(), bagSort.name() + "Item")
              .add(Att.WRAP_ELEMENT(), "<" + cellName + ">")
              .add(Att.UNIT(), "." + bagSort.name())
              .add(Att.HOOK(), type.toUpperCase() + ".concat")
              .add(Att.AVOID()) // needed to ensure cell collections are parsed as Bag instead of
              // CellBag
              .add(Att.FUNCTION());
      String unitHook = type.toUpperCase() + ".unit", elementHook = type.toUpperCase() + ".element";
      switch (type) {
        case "Set":
          bagAtt = bagAtt.add(Att.IDEM(), "");
          // fall through
        case "Map":
          bagAtt = bagAtt.add(Att.COMM(), "");
          break;
        case "Bag":
          bagAtt = bagAtt.add(Att.COMM(), "").add(Att.BAG());
          break;
        case "List":
          break;
        default:
          throw KEMException.compilerError(
              "Unexpected type for multiplicity * cell: "
                  + cellName
                  + ". Should be one of: Set, Bag, List, Map",
              KApply(KLabel("#EmptyK"), Seq(), configAtt));
      }
      SyntaxSort sortDecl =
          SyntaxSort(
              Seq(),
              bagSort,
              Att.empty()
                  .add(Att.HOOK(), type.toUpperCase() + '.' + type)
                  .add(Att.CELL_COLLECTION()));
      Sentence bagSubsort = Production(Seq(), bagSort, Seq(NonTerminal(sort)));
      Sentence bagElement;
      if (type.equals("Map")) {
        if (childSorts.isEmpty()) {
          throw KEMException.compilerError(
              "Cells of type Map expect at least one child cell as their key",
              KApply(KLabel("#EmptyK"), Seq(), configAtt));
        }
        bagElement =
            Production(
                KLabel(bagSort.name() + "Item"),
                bagSort,
                Seq(
                    Terminal(bagSort.name() + "Item"),
                    Terminal("("),
                    NonTerminal(childSorts.get(0)),
                    Terminal(","),
                    NonTerminal(sort),
                    Terminal(")")),
                Att.empty()
                    .add(Att.HOOK(), elementHook)
                    .add(Att.FUNCTION())
                    .add(Att.FORMAT(), "%5"));
      } else {
        bagElement =
            Production(
                KLabel(bagSort.name() + "Item"),
                bagSort,
                Seq(
                    Terminal(bagSort.name() + "Item"),
                    Terminal("("),
                    NonTerminal(sort),
                    Terminal(")")),
                Att.empty()
                    .add(Att.HOOK(), elementHook)
                    .add(Att.FUNCTION())
                    .add(Att.FORMAT(), "%3"));
      }
      Sentence bagUnit =
          Production(
              KLabel("." + bagSort.name()),
              bagSort,
              Seq(Terminal("." + bagSort.name())),
              Att.empty().add(Att.HOOK(), unitHook).add(Att.FUNCTION()));
      Sentence bag =
          Production(
              KLabel("_" + bagSort + "_"),
              bagSort,
              Seq(NonTerminal(bagSort), NonTerminal(bagSort)),
              bagAtt);
      sentences.add(sortDecl);
      sentences.add(bagSubsort);
      sentences.add(bagElement);
      sentences.add(bagUnit);
      sentences.add(bag);
      if (type.equals("Map")) {
        // syntax Bool ::= KeyCell "in_keys" "(" CellMap ")" [function, total, hook(MAP.in_keys)]
        sentences.add(
            Production(
                KLabel(bagSort.name() + ":in_keys"),
                Sorts.Bool(),
                Seq(
                    NonTerminal(childSorts.get(0)),
                    Terminal("in_keys"),
                    Terminal("("),
                    NonTerminal(bagSort),
                    Terminal(")")),
                Att.empty().add(Att.HOOK(), "MAP.in_keys").add(Att.FUNCTION()).add(Att.TOTAL())));

        // syntax KeyCell ::= CellMapKey(Cell) [function, total]
        // rule CellMapKey(<cell> K ...<\cell>) => K
        KLabel cellMapKeyLabel = KLabel(bagSort.name() + "Key");
        Production cellMapKeyProduction =
            Production(
                cellMapKeyLabel,
                childSorts.get(0),
                Seq(
                    Terminal(bagSort.name() + "Key"),
                    Terminal("("),
                    NonTerminal(sort),
                    Terminal(")")),
                Att.empty().add(Att.FUNCTION()).add(Att.TOTAL()));
        KVariable key =
            KVariable("Key", Att.empty().add(Att.SORT(), Sort.class, childSorts.get(0)));
        Rule cellMapKeyRule =
            Rule(
                KRewrite(
                    KApply(
                        cellMapKeyLabel,
                        IncompleteCellUtils.make(KLabel(klabel), false, key, true)),
                    key),
                BooleanUtils.TRUE,
                BooleanUtils.TRUE);
        sentences.add(cellMapKeyProduction);
        sentences.add(cellMapKeyRule);
      }
      // rule initCell => .CellBag
      // -or-
      // rule initCell(Init) => <cell> Context[$var] </cell>
      cellsSort = bagSort;
      rhs =
          optionalCellInitializer(
              kem, cellName, hasConfigurationOrRegularVariable, cellProperties, initLabel);
    } else if (multiplicity == Multiplicity.OPTIONAL) {
      // syntax Cell ::= ".Cell"
      Production cellUnit = Production(KLabel("." + sortName), sort, Seq(Terminal("." + sortName)));
      sentences.add(cellUnit);
      // add UNIT attribute to cell production.
      if (!m.definedKLabels().contains(KLabel(klabel))) {
        Production cellProduction =
            Production(
                KLabel(klabel),
                sort,
                immutable(items),
                att.add(Att.UNIT(), cellUnit.klabel().get().name()));
        sentences.add(cellProduction);
      }
      // rule initCell => .CellBag
      // -or-
      // rule initCell(Init) => <cell> Context[$var] </cell>
      cellsSort = sort;
      rhs =
          optionalCellInitializer(
              kem, cellName, hasConfigurationOrRegularVariable, cellProperties, initLabel);
    } else {
      // rule initCell => <cell> initChildren... </cell>
      // -or-
      // rule initCell(Init) => <cell> initChildren(Init)... </cell>
      cellsSort = sort;
      if (hasConfigurationOrRegularVariable || isStream) {
        rhs = KApply(KLabel(initLabel), INIT);
      } else {
        rhs = KApply(KLabel(initLabel));
      }
    }

    if (cellProperties.contains(Att.EXIT())) {
      KLabel getExitCodeLabel = KLabel("getExitCode");
      Production getExitCode =
          Production(
              getExitCodeLabel,
              Sorts.Int(),
              Seq(
                  Terminal("getExitCode"),
                  Terminal("("),
                  NonTerminal(Sorts.GeneratedTopCell()),
                  Terminal(")")),
              Att.empty().add(Att.FUNCTION()));
      sentences.add(getExitCode);
      KVariable var = KVariable("Exit", Att.empty().add(Att.SORT(), Sort.class, Sorts.Int()));
      Rule getExitCodeRule =
          Rule(
              KRewrite(
                  KApply(
                      getExitCodeLabel,
                      IncompleteCellUtils.make(
                          KLabels.GENERATED_TOP_CELL,
                          true,
                          IncompleteCellUtils.make(KLabel(klabel), false, var, false),
                          true)),
                  var),
              BooleanUtils.TRUE,
              BooleanUtils.TRUE);
      sentences.add(SyntaxSort.apply(Seq(), Sorts.GeneratedTopCell(), Att.empty()));
      sentences.add(getExitCodeRule);
    }
    return Tuple4.apply(immutable(sentences), cellsSort, rhs, false);
  }

  /**
   * Returns the term used to initialize an optinoal cell. An optional cell is initialized to the
   * empty bag if it contains no configuration variables, and to a single cell if it contains
   * configuration variables.
   */
  private static KApply optionalCellInitializer(
      KExceptionManager kem,
      String cellName,
      boolean initializeOptionalCell,
      Att cellProperties,
      String initLabel) {
    if (initializeOptionalCell) {
      if (!cellProperties.contains(Att.INITIAL())) {
        kem.registerCompilerWarning(
            KException.ExceptionType.CELL_COLLECTION_VAR_WITHOUT_INITIAL,
            "Configuration variable found in declaration of collection cell <"
                + cellName
                + ">. Implicitly, this causes the initial configuration to start with one <"
                + cellName
                + "> element instead of zero. Add the `initial=\"\"` attribute to make that behavior explicit.");
      }
      return KApply(KLabel(initLabel), INIT);
    } else if (cellProperties.contains(Att.INITIAL())) {
      return KApply(KLabel(initLabel));
    } else {
      return KApply(KLabels.CELLS);
    }
  }

  private static Att getCellPropertiesAsAtt(K k, String cellName) {
    Att att = Att.empty();
    if (cellName.equals("k")) {
      att = att.add(Att.MAINCELL());
    }
    att = att.add(Att.CELL()).add(Att.CELL_NAME(), cellName);
    return att.addAll(getCellPropertiesAsAtt(k));
  }

  private static Att getCellPropertiesAsAtt(K k) {
    if (k instanceof KApply kapp) {
      if (kapp.klabel().name().equals("#cellPropertyListTerminator")) {
        return Att.empty();
      } else if (kapp.klabel().name().equals("#cellPropertyList")) {
        if (kapp.klist().size() == 2) {
          Tuple2<Att.Key, String> attribute = getCellProperty(kapp.klist().items().get(0));
          return Att.empty()
              .add(attribute._1(), attribute._2())
              .addAll(getCellPropertiesAsAtt(kapp.klist().items().get(1)));
        }
      }
    }
    throw KEMException.compilerError("Malformed cell properties", k);
  }

  private static Tuple2<Att.Key, String> getCellProperty(K k) {
    if (k instanceof KApply kapp) {
      if (kapp.klabel().name().equals("#cellProperty")) {
        if (kapp.klist().size() == 2) {
          if (kapp.klist().items().get(0) instanceof KToken keyToken) {
            if (keyToken.sort().equals(Sort("#CellName"))) {
              Att.Key key =
                  Att.getBuiltinKeyOptional(keyToken.s())
                      .orElseThrow(
                          () ->
                              KEMException.compilerError(
                                  "Unrecognized property: " + keyToken.s(), k));
              if (kapp.klist().items().get(0) instanceof KToken) {
                KToken valueToken = (KToken) kapp.klist().items().get(1);
                if (valueToken.sort().equals(Sorts.KString())) {
                  String value = StringUtil.unquoteKString(valueToken.s());
                  return Tuple2.apply(key, value);
                }
              }
            }
          }
        }
      }
    }
    throw KEMException.compilerError("Malformed cell property", k);
  }

  public static String getSortOfCell(String cellName) {
    char[] chars = cellName.toCharArray();
    StringBuilder sb = new StringBuilder();
    sb.append(Character.toUpperCase(chars[0]));
    for (int i = 1; i < chars.length; i++) {
      if (chars[i] == '-' && i + 1 < chars.length && Character.isLowerCase(chars[i + 1])) {
        chars[i + 1] = Character.toUpperCase(chars[i + 1]);
      } else if (chars[i] != '-') {
        sb.append(chars[i]);
      }
    }
    sb.append("Cell");
    return sb.toString();
  }

  private static Multiplicity convertStringMultiplicity(Option<String> multiplicity, K body) {
    if (multiplicity.isEmpty()) return Multiplicity.ONE;
    try {
      return Multiplicity.of(multiplicity.get());
    } catch (IllegalArgumentException x) {
      throw KEMException.compilerError(
          "Invalid multiplicity found in cell: " + multiplicity.get(), body);
    }
  }
}

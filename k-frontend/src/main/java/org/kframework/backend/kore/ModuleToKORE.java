// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.kore;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.SetMultimap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Hooks;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.ComputeTransitiveFunctionDependencies;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.NumberSentences;
import org.kframework.compile.RefreshRules;
import org.kframework.compile.RewriteToTop;
import org.kframework.definition.Claim;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.definition.Tag;
import org.kframework.definition.Terminal;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.kore.VisitK;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import scala.Option;
import scala.Tuple2;
import scala.collection.JavaConverters;

class RuleInfo {
  boolean isEquation;
  boolean isOwise;
  boolean isCeil;
  Production production;
  String productionSortStr;
  List<Sort> prodChildrenSorts;
  KLabel productionLabel;
  List<K> leftChildren;

  public RuleInfo(
      boolean equation,
      boolean owise,
      boolean ceil,
      Production production,
      String prodSortStr,
      List<Sort> prodChildrenSorts,
      KLabel prodLabel,
      List<K> leftChildren) {
    this.isEquation = equation;
    this.isOwise = owise;
    this.isCeil = ceil;
    this.production = production;
    this.productionSortStr = prodSortStr;
    this.prodChildrenSorts = prodChildrenSorts;
    this.productionLabel = prodLabel;
    this.leftChildren = leftChildren;
  }
}

public class ModuleToKORE {
  public enum SentenceType {
    REWRITE_RULE,
    ONE_PATH,
    ALL_PATH
  }

  public static final String ONE_PATH_OP = KLabels.RL_wEF.name();
  public static final String ALL_PATH_OP = KLabels.RL_wAF.name();
  private final Module module;
  private final Set<String> impureFunctions = new HashSet<>();
  private final AddSortInjections addSortInjections;
  private final KLabel topCellInitializer;
  private final Set<String> mlBinders = new HashSet<>();
  private final KompileOptions options;

  // for now these two variables are coupled to enable the functional claim check
  private final KExceptionManager kem;
  private final boolean allowFuncClaims;

  public ModuleToKORE(Module module, KLabel topCellInitializer, KompileOptions options) {
    this(module, topCellInitializer, options, null, false);
  }

  public ModuleToKORE(
      Module module,
      KLabel topCellInitializer,
      KompileOptions options,
      KExceptionManager kem,
      boolean allowFuncClaims) {
    this.kem = kem;
    this.allowFuncClaims = allowFuncClaims;
    this.module = module;
    this.addSortInjections = new AddSortInjections(module);
    this.topCellInitializer = topCellInitializer;
    this.options = options;
    for (Production prod : iterable(module.sortedProductions())) {
      if (prod.att().contains(Att.ML_BINDER())) {
        mlBinders.add(prod.klabel().get().name());
      }
    }
  }

  private static final boolean METAVAR = false;

  public void convert(
      boolean heatCoolEq,
      String prelude,
      StringBuilder semantics,
      StringBuilder syntax,
      StringBuilder macros) {
    Sort topCellSort = Sorts.GeneratedTopCell();
    String topCellSortStr = getSortStr(topCellSort);
    semantics.append("[topCellInitializer{}(");
    convert(topCellInitializer, semantics);
    semantics.append("()), ");
    StringBuilder sb = new StringBuilder();
    HashMap<Att.Key, Boolean> considerSource = new HashMap<>();
    considerSource.put(Att.SOURCE(), true);
    // insert the location of the main module so the backend can provide better error location
    convert(
        considerSource,
        Att.empty().add(Att.SOURCE(), Source.class, module.att().get(Att.SOURCE(), Source.class)),
        sb,
        null,
        null);
    semantics.append(sb.subSequence(1, sb.length() - 1));
    semantics.append("]\n\n");

    semantics.append(prelude);
    semantics.append("\n");

    SentenceType sentenceType = getSentenceType(module.att()).orElse(SentenceType.REWRITE_RULE);
    semantics.append("module ");
    convert(module.name(), semantics);
    semantics.append("\n\n// imports\n");
    semantics.append("  import K []\n\n// sorts\n");

    Set<SortHead> tokenSorts = new HashSet<>();
    // Map attribute name to whether the attribute has a value
    Map<Att.Key, Boolean> attributes = new HashMap<>();
    attributes.put(Att.NAT(), true);
    attributes.put(Att.TERMINALS(), true);
    attributes.put(Att.COLORS(), true);
    attributes.put(Att.PRIORITY(), true);
    Set<Integer> priorities = new HashSet<>();
    collectTokenSortsAndAttributes(tokenSorts, attributes, priorities, heatCoolEq, topCellSortStr);
    Map<Integer, String> priorityToPreviousGroup = new HashMap<>();
    List<Integer> priorityList = new ArrayList<>(priorities);
    java.util.Collections.sort(priorityList);
    if (priorityList.size() > 0) {
      priorityToPreviousGroup.put(priorityList.get(0), "");
    }
    for (int i = 1; i < priorityList.size(); i++) {
      Integer previous = priorityList.get(i - 1);
      Integer current = priorityList.get(i);
      priorityToPreviousGroup.put(current, String.format("priorityLE%d", previous));
    }

    Set<String> collectionSorts = new HashSet<>();
    collectionSorts.add("SET.Set");
    collectionSorts.add("MAP.Map");
    collectionSorts.add("LIST.List");
    collectionSorts.add("RANGEMAP.RangeMap");
    attributes.remove(Att.HAS_DOMAIN_VALUES());
    if (attributes.containsKey(Att.TOKEN())) {
      attributes.put(Att.HAS_DOMAIN_VALUES(), false);
    }
    translateSorts(tokenSorts, attributes, collectionSorts, semantics);

    List<Rule> sortedRules = new ArrayList<>(JavaConverters.seqAsJavaList(module.sortedRules()));
    if (options.backend.equals("haskell")) {
      module
          .sortedProductions()
          .toStream()
          .filter(this::isGeneratedInKeysOp)
          .foreach(
              prod -> {
                if (!options.disableCeilSimplificationRules) {
                  genMapCeilAxioms(prod, sortedRules);
                }
                return prod;
              });
    }
    SetMultimap<KLabel, Rule> functionRules = HashMultimap.create();
    for (Rule rule : sortedRules) {
      K left = RewriteToTop.toLeft(rule.body());
      if (left instanceof KApply kapp) {
        Production prod = production(kapp);
        if (prod.att().contains(Att.FUNCTION())
            || rule.att().contains(Att.ANYWHERE())
            || ExpandMacros.isMacro(rule)) {
          functionRules.put(kapp.klabel(), rule);
        }
      }
    }
    ComputeTransitiveFunctionDependencies deps = new ComputeTransitiveFunctionDependencies(module);
    Set<KLabel> impurities =
        stream(module.sortedProductions())
            .filter(prod -> prod.klabel().isDefined() && prod.att().contains(Att.IMPURE()))
            .filter(prod -> prod.att().contains(Att.IMPURE()))
            .map(prod -> prod.klabel().get())
            .collect(Collectors.toSet());
    impurities.addAll(deps.ancestors(impurities));

    semantics.append("\n// symbols\n");
    Set<Production> overloads = new HashSet<>();
    for (Production lesser : module.overloads().elements()) {
      overloads.addAll(module.overloads().relations().getOrDefault(lesser, Set.of()));
    }

    syntax.append(semantics);
    translateSymbols(attributes, functionRules, impurities, overloads, semantics, false);
    translateSymbols(attributes, functionRules, impurities, overloads, syntax, true);

    // print syntax definition
    for (Tuple2<Sort, scala.collection.immutable.List<Production>> sort :
        iterable(module.bracketProductionsFor())) {
      for (Production prod : iterable(sort._2())) {
        translateSymbol(
            attributes,
            functionRules,
            impurities,
            overloads,
            prod.att().get(Att.BRACKET_LABEL(), KLabel.class),
            prod,
            syntax,
            true);
      }
    }
    for (Production prod : iterable(module.sortedProductions())) {
      if (isBuiltinProduction(prod)) {
        continue;
      }
      if (prod.isSubsort() && !prod.sort().equals(Sorts.K())) {
        genSubsortAxiom(prod, syntax);
        continue;
      }
    }

    for (Production lesser : module.overloads().elements()) {
      for (Production greater : module.overloads().relations().getOrDefault(lesser, Set.of())) {
        genOverloadedAxiom(lesser, greater, syntax);
      }
    }

    syntax.append("endmodule []\n");

    semantics.append("\n// generated axioms\n");
    Set<Tuple2<Production, Production>> noConfusion = new HashSet<>();
    for (Production prod : iterable(module.sortedProductions())) {
      if (isBuiltinProduction(prod)) {
        continue;
      }
      if (prod.isSubsort() && !prod.sort().equals(Sorts.K())) {
        genSubsortAxiom(prod, semantics);
        continue;
      }
      if (prod.klabel().isEmpty()) {
        continue;
      }
      if (prod.att().contains(Att.ASSOC())) {
        genAssocAxiom(prod, semantics);
      }
      // if (prod.att().contains(Att.COMM())) {
      //    genCommAxiom(prod, semantics);
      // }
      if (prod.att().contains(Att.IDEM())) {
        genIdemAxiom(prod, semantics);
      }
      if (isFunction(prod) && prod.att().contains(Att.UNIT())) {
        genUnitAxiom(prod, semantics);
      }
      if (isFunctional(prod)) {
        genFunctionalAxiom(prod, semantics);
      }
      if (isConstructor(prod, functionRules, impurities)) {
        genNoConfusionAxioms(prod, noConfusion, functionRules, impurities, semantics);
      }
    }

    for (Sort sort : iterable(module.sortedAllSorts())) {
      genNoJunkAxiom(sort, semantics);
    }

    for (Production lesser : module.overloads().elements()) {
      for (Production greater : module.overloads().relations().getOrDefault(lesser, Set.of())) {
        genOverloadedAxiom(lesser, greater, semantics);
      }
    }

    semantics.append("\n// rules\n");

    macros.append("// macros\n");
    int ruleIndex = 0;
    ListMultimap<Integer, String> priorityToAlias = ArrayListMultimap.create();
    for (Rule rule : sortedRules) {
      if (ExpandMacros.isMacro(rule)) {
        convertRule(
            rule,
            ruleIndex,
            heatCoolEq,
            topCellSortStr,
            attributes,
            functionRules,
            priorityToPreviousGroup,
            priorityToAlias,
            sentenceType,
            macros);
      } else {
        convertRule(
            rule,
            ruleIndex,
            heatCoolEq,
            topCellSortStr,
            attributes,
            functionRules,
            priorityToPreviousGroup,
            priorityToAlias,
            sentenceType,
            semantics);
      }
      ruleIndex++;
    }

    if (options.enableKoreAntileft) {
      semantics.append("\n// priority groups\n");
      genPriorityGroups(
          priorityList, priorityToPreviousGroup, priorityToAlias, topCellSortStr, semantics);
    }

    semantics.append("endmodule ");
    convert(attributes, module.att().remove(Att.DIGEST()), semantics, null, null);
    semantics.append("\n");
  }

  private void collectTokenSortsAndAttributes(
      Set<SortHead> tokenSorts,
      Map<Att.Key, Boolean> attributes,
      Set<Integer> priorities,
      boolean heatCoolEq,
      String topCellSortStr) {
    for (SortHead sort : iterable(module.sortedDefinedSorts())) {
      Att att = module.sortAttributesFor().get(sort).getOrElse(() -> Att.empty());
      if (att.contains(Att.TOKEN())) {
        tokenSorts.add(sort);
      }
      collectAttributes(attributes, att);
    }
    for (Production prod : iterable(module.sortedProductions())) {
      Att att = prod.att();
      if (att.contains(Att.TOKEN())) {
        tokenSorts.add(prod.sort().head());
      }
      collectAttributes(attributes, att);
    }
    for (Rule r : iterable(module.sortedRules())) {
      Att att = r.att();
      collectAttributes(attributes, att);
      RuleInfo ruleInfo = getRuleInfo(r, heatCoolEq, topCellSortStr);
      // only collect priorities of semantics rules
      if (!ruleInfo.isEquation && !ExpandMacros.isMacro(r)) {
        priorities.add(getPriority(att));
      }
    }
  }

  private void translateSorts(
      Set<SortHead> tokenSorts,
      Map<Att.Key, Boolean> attributes,
      Set<String> collectionSorts,
      StringBuilder sb) {
    for (SortHead sort : iterable(module.sortedDefinedSorts())) {
      if (sort.equals(Sorts.K().head()) || sort.equals(Sorts.KItem().head())) {
        continue;
      }
      sb.append("  ");
      Att att = module.sortAttributesFor().get(sort).getOrElse(() -> Att.empty());
      if (att.contains(Att.HOOK())) {
        if (collectionSorts.contains(att.get(Att.HOOK()))) {
          Production concatProd =
              stream(module.productionsForSort().apply(sort))
                  .filter(p -> p.att().contains(Att.ELEMENT()))
                  .findAny()
                  .get();
          att =
              att.add(Att.ELEMENT(), K.class, KApply(KLabel(concatProd.att().get(Att.ELEMENT()))));
          att = att.add(Att.CONCAT(), K.class, KApply(concatProd.klabel().get()));
          att = att.add(Att.UNIT(), K.class, KApply(KLabel(concatProd.att().get(Att.UNIT()))));
          if (concatProd.att().contains(Att.UPDATE())) {
            att =
                att.add(Att.UPDATE(), K.class, KApply(KLabel(concatProd.att().get(Att.UPDATE()))));
          }
          sb.append("hooked-");
        } else {
          sb.append("hooked-");
        }
      }
      att = att.remove(Att.HAS_DOMAIN_VALUES());
      if (tokenSorts.contains(sort)) {
        att = att.add(Att.HAS_DOMAIN_VALUES());
      }
      if (sort.params() == 0 && Sort(sort).isNat()) {
        att = att.add(Att.NAT(), sort.name());
      }
      sb.append("sort ");
      convert(sort, sb);
      sb.append(" ");
      convert(attributes, att, sb, null, null);
      sb.append("\n");
    }
  }

  private void translateSymbols(
      Map<Att.Key, Boolean> attributes,
      SetMultimap<KLabel, Rule> functionRules,
      Set<KLabel> impurities,
      Set<Production> overloads,
      StringBuilder sb,
      boolean withSyntaxAtts) {
    for (Production prod : iterable(module.sortedProductions())) {
      if (isBuiltinProduction(prod)) {
        continue;
      }
      if (prod.klabel().isEmpty()) {
        continue;
      }
      if (impurities.contains(prod.klabel().get())) {
        impureFunctions.add(prod.klabel().get().name());
      }
      translateSymbol(
          attributes,
          functionRules,
          impurities,
          overloads,
          prod.klabel().get(),
          prod,
          sb,
          withSyntaxAtts);
    }
  }

  private void translateSymbol(
      Map<Att.Key, Boolean> attributes,
      SetMultimap<KLabel, Rule> functionRules,
      Set<KLabel> impurities,
      Set<Production> overloads,
      KLabel label,
      Production prod,
      StringBuilder sb,
      boolean withSyntaxAtts) {
    sb.append("  ");
    if (isFunction(prod) && isHook(prod)) {
      sb.append("hooked-");
    }
    sb.append("symbol ");
    convert(label, prod.params(), sb);
    String conn;
    sb.append("(");
    conn = "";
    for (NonTerminal nt : iterable(prod.nonterminals())) {
      Sort sort = nt.sort();
      sb.append(conn);
      convert(sort, prod, sb);
      conn = ", ";
    }
    sb.append(") : ");
    convert(prod.sort(), prod, sb);
    sb.append(" ");
    Att koreAtt = koreAttributes(prod, functionRules, impurities, overloads, withSyntaxAtts);
    convert(attributes, koreAtt, sb, null, null);
    sb.append("\n");
  }

  private void genSubsortAxiom(Production prod, StringBuilder sb) {
    Production finalProd = prod;
    functionalPattern(
        prod,
        () -> {
          sb.append("inj{");
          convert(finalProd.getSubsortSort(), finalProd, sb);
          sb.append(", ");
          convert(finalProd.sort(), finalProd, sb);
          sb.append("} (From:");
          convert(finalProd.getSubsortSort(), finalProd, sb);
          sb.append(")");
        },
        sb);
    sb.append(" [subsort{");
    convert(prod.getSubsortSort(), prod, sb);
    sb.append(", ");
    convert(prod.sort(), prod, sb);
    sb.append("}()] // subsort\n");
  }

  private void genAssocAxiom(Production prod, StringBuilder sb) {
    // s(s(K1,K2),K3) = s(K1,s(K2,K3))
    if (prod.arity() != 2) {
      throw KEMException.compilerError(
          "Found a non-binary production with the assoc attribute", prod);
    }
    if (!(module.subsorts().lessThanEq(prod.sort(), prod.nonterminal(0).sort())
        && module.subsorts().lessThanEq(prod.sort(), prod.nonterminal(1).sort()))) {
      throw KEMException.compilerError(
          "Found an associative production with ill formed sorts", prod);
    }
    sb.append("  axiom");
    convertParams(prod.klabel(), true, sb);
    sb.append(" \\equals{");
    convert(prod.sort(), prod, sb);
    sb.append(", R} (");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(K1:");
    convert(prod.sort(), prod, sb);
    sb.append(",K2:");
    convert(prod.sort(), prod, sb);
    sb.append("),K3:");
    convert(prod.sort(), prod, sb);
    sb.append("),");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(K1:");
    convert(prod.sort(), prod, sb);
    sb.append(",");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(K2:");
    convert(prod.sort(), prod, sb);
    sb.append(",K3:");
    convert(prod.sort(), prod, sb);
    sb.append("))) [assoc{}()] // associativity\n");
  }

  private void genCommAxiom(Production prod, StringBuilder sb) {
    // s(K1, K2) = s(K2, K1)
    if (prod.arity() != 2) {
      throw KEMException.compilerError(
          "Found a non-binary production with the comm attribute", prod);
    }
    if (!(prod.nonterminal(0).sort().equals(prod.nonterminal(1).sort()))) {
      throw KEMException.compilerError(
          "Found a commutative production with ill formed sorts", prod);
    }
    Sort childSort = prod.nonterminal(0).sort();
    sb.append("  axiom");
    convertParams(prod.klabel(), true, sb);
    sb.append(" \\equals{");
    convert(prod.sort(), prod, sb);
    sb.append(", R} (");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(K1:");
    convert(childSort, prod, sb);
    sb.append(",K2:");
    convert(childSort, prod, sb);
    sb.append("),");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(K2:");
    convert(childSort, prod, sb);
    sb.append(",K1:");
    convert(childSort, prod, sb);
    sb.append(")) [comm{}()] // commutativity\n");
  }

  private void genIdemAxiom(Production prod, StringBuilder sb) {
    // s(K, K) = K
    if (prod.arity() != 2) {
      throw KEMException.compilerError(
          "Found a non-binary production with the assoc attribute", prod);
    }
    if (!(prod.sort().equals(prod.nonterminal(0).sort())
        && prod.sort().equals(prod.nonterminal(1).sort()))) {
      throw KEMException.compilerError(
          "Found an associative production with ill formed sorts", prod);
    }
    sb.append("  axiom");
    convertParams(prod.klabel(), true, sb);
    sb.append(" \\equals{");
    convert(prod.sort(), prod, sb);
    sb.append(", R} (");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(K:");
    convert(prod.sort(), prod, sb);
    sb.append(",K:");
    convert(prod.sort(), prod, sb);
    sb.append("),K:");
    convert(prod.sort(), prod, sb);
    sb.append(") [idem{}()] // idempotency\n");
  }

  private void genUnitAxiom(Production prod, StringBuilder sb) {
    // s(K, unit) = K
    // s(unit, K) = K
    if (prod.arity() != 2) {
      throw KEMException.compilerError(
          "Found a non-binary production with the assoc attribute", prod);
    }
    if (!(prod.sort().equals(prod.nonterminal(0).sort())
        && prod.sort().equals(prod.nonterminal(1).sort()))) {
      throw KEMException.compilerError(
          "Found an associative production with ill formed sorts", prod);
    }
    KLabel unit = KLabel(prod.att().get(Att.UNIT()));
    sb.append("  axiom");
    convertParams(prod.klabel(), true, sb);
    sb.append("\\equals{");
    convert(prod.sort(), prod, sb);
    sb.append(", R} (");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(K:");
    convert(prod.sort(), prod, sb);
    sb.append(",");
    convert(unit, sb);
    sb.append("()),K:");
    convert(prod.sort(), prod, sb);
    sb.append(") [unit{}()] // right unit\n");

    sb.append("  axiom");
    convertParams(prod.klabel(), true, sb);
    sb.append("\\equals{");
    convert(prod.sort(), prod, sb);
    sb.append(", R} (");
    convert(prod.klabel().get(), prod, sb);
    sb.append("(");
    convert(unit, sb);
    sb.append("(),K:");
    convert(prod.sort(), prod, sb);
    sb.append("),K:");
    convert(prod.sort(), prod, sb);
    sb.append(") [unit{}()] // left unit\n");
  }

  private void genMapCeilAxioms(Production prod, Collection<Rule> rules) {
    Sort mapSort = prod.nonterminal(1).sort();
    scala.collection.Set<Production> mapProds = module.productionsForSort().apply(mapSort.head());
    Production concatProd = mapProds.find(p -> hasHookValue(p.att(), "MAP.concat")).get();
    Production elementProd = mapProds.find(p -> hasHookValue(p.att(), "MAP.element")).get();
    scala.collection.immutable.Seq<NonTerminal> nonterminals = elementProd.nonterminals();
    Sort sortParam = Sort(AddSortInjections.SORTPARAM_NAME, Sort("Q"));

    // rule
    //   #Ceil(MapItem(K1, K2, ..., Kn) Rest:Map)
    // =>
    //  {(@K1 in_keys(@Rest)) #Equals false} #And #Ceil(@K2) #And ... #And #Ceil(@Kn)
    // Note: The {_ in_keys(_) #Equals false} condition implies
    // #Ceil(@K1) and #Ceil(@Rest).
    // [simplification]

    K restMapSet = KVariable("@Rest", Att.empty().add(Att.SORT(), Sort.class, mapSort));
    KLabel ceilMapLabel = KLabel(KLabels.ML_CEIL.name(), mapSort, sortParam);
    KLabel andLabel = KLabel(KLabels.ML_AND.name(), sortParam);

    // arguments of MapItem and their #Ceils
    List<K> setArgs = new ArrayList<>();
    K setArgsCeil = KApply(KLabel(KLabels.ML_TRUE.name(), sortParam));
    for (int i = 0; i < nonterminals.length(); i++) {
      Sort sort = nonterminals.apply(i).sort();
      KVariable setVar = KVariable("@K" + i, Att.empty().add(Att.SORT(), Sort.class, sort));
      setArgs.add(setVar);
      if (i > 0) {
        KLabel ceil = KLabel(KLabels.ML_CEIL.name(), sort, sortParam);
        setArgsCeil = KApply(andLabel, setArgsCeil, KApply(ceil, setVar));
      }
    }
    scala.collection.immutable.Seq<K> setArgsSeq = immutable(setArgs);

    KLabel equalsLabel = KLabel(KLabels.ML_EQUALS.name(), Sorts.Bool(), sortParam);
    Rule ceilMapRule =
        Rule(
            KRewrite(
                KApply(
                    ceilMapLabel,
                    KApply(
                        concatProd.klabel().get(),
                        KApply(elementProd.klabel().get(), setArgsSeq, Att.empty()),
                        restMapSet)),
                KApply(
                    andLabel,
                    KApply(
                        equalsLabel,
                        KApply(prod.klabel().get(), setArgs.get(0), restMapSet),
                        BooleanUtils.FALSE),
                    setArgsCeil)),
            BooleanUtils.TRUE,
            BooleanUtils.TRUE,
            Att.empty().add(Att.SIMPLIFICATION()));
    ceilMapRule = (Rule) NumberSentences.number(ceilMapRule);
    rules.add(ceilMapRule);
  }

  static boolean hasHookValue(Att atts, String value) {
    return atts.contains(Att.HOOK()) && atts.get(Att.HOOK()).equals(value);
  }

  private void genFunctionalAxiom(Production prod, StringBuilder sb) {
    // exists y . f(...) = y
    Production finalProd = prod;
    functionalPattern(prod, () -> applyPattern(finalProd, "K", sb), sb);
    sb.append(" [functional{}()] // functional\n");
  }

  private void genNoConfusionAxioms(
      Production prod,
      Set<Tuple2<Production, Production>> noConfusion,
      SetMultimap<KLabel, Rule> functionRulesMap,
      Set<KLabel> impurities,
      StringBuilder sb) {
    // c(x1,x2,...) /\ c(y1,y2,...) -> c(x1/\y2,x2/\y2,...)
    if (prod.arity() > 0) {
      sb.append("  axiom");
      convertParams(prod.klabel(), false, sb);
      sb.append("\\implies{");
      convert(prod.sort(), prod, sb);
      sb.append("} (\\and{");
      convert(prod.sort(), prod, sb);
      sb.append("} (");
      applyPattern(prod, "X", sb);
      sb.append(", ");
      applyPattern(prod, "Y", sb);
      sb.append("), ");
      convert(prod.klabel().get(), prod, sb);
      sb.append("(");
      String conn = "";
      for (int i = 0; i < prod.arity(); i++) {
        sb.append(conn);
        sb.append("\\and{");
        convert(prod.nonterminal(i).sort(), prod, sb);
        sb.append("} (X").append(i).append(":");
        convert(prod.nonterminal(i).sort(), prod, sb);
        sb.append(", Y").append(i).append(":");
        convert(prod.nonterminal(i).sort(), prod, sb);
        sb.append(")");
        conn = ", ";
      }
      sb.append(")) [constructor{}()] // no confusion same constructor\n");
    }

    for (Production prod2 :
        Collections.mutable(module.productionsForSort().apply(prod.sort().head())).stream()
            .sorted(Production.ord())
            .toList()) {
      // !(cx(x1,x2,...) /\ cy(y1,y2,...))
      if (prod2.klabel().isEmpty()
          || noConfusion.contains(Tuple2.apply(prod, prod2))
          || prod.equals(prod2)
          || !isConstructor(prod2, functionRulesMap, impurities)
          || isBuiltinProduction(prod2)) {
        // TODO (traiansf): add no confusion axioms for constructor vs inj.
        continue;
      }
      noConfusion.add(Tuple2.apply(prod, prod2));
      noConfusion.add(Tuple2.apply(prod2, prod));
      sb.append("  axiom");
      convertParams(prod.klabel(), false, sb);
      sb.append("\\not{");
      convert(prod.sort(), prod, sb);
      sb.append("} (\\and{");
      convert(prod.sort(), prod, sb);
      sb.append("} (");
      applyPattern(prod, "X", sb);
      sb.append(", ");
      applyPattern(prod2, "Y", sb);
      sb.append(")) [constructor{}()] // no confusion different constructors\n");
    }
  }

  public static int getPriority(Att att) {
    if (att.contains(Att.PRIORITY())) {
      try {
        return Integer.parseInt(att.get(Att.PRIORITY()));
      } catch (NumberFormatException e) {
        throw KEMException.compilerError(
            "Invalid value for priority attribute: "
                + att.get(Att.PRIORITY())
                + ". Must be an integer.",
            e);
      }
    } else if (att.contains(Att.OWISE())) {
      return 200;
    }
    return 50;
  }

  private void genNoJunkAxiom(Sort sort, StringBuilder sb) {
    StringBuilder sbTemp = new StringBuilder();
    sbTemp.append("  axiom{} ");
    boolean hasToken = false;
    int numTerms = 0;
    sbTemp.append("\\or{");
    convert(sort, sbTemp);
    sbTemp.append("} (");
    for (Production prod :
        mutable(mutable(module.productionsForSort()).getOrDefault(sort.head(), Set())).stream()
            .sorted(Production.ord())
            .toList()) {
      if (isFunction(prod) || prod.isSubsort() || isBuiltinProduction(prod) || prod.isMacro()) {
        continue;
      }
      if (prod.klabel().isEmpty()
          && !((prod.att().contains(Att.TOKEN()) && !hasToken) || prod.isSubsort())) {
        continue;
      }
      numTerms++;
      if (prod.att().contains(Att.TOKEN()) && !hasToken) {
        convertTokenProd(sort, sbTemp);
        hasToken = true;
      } else if (prod.klabel().isDefined()) {
        for (int i = 0; i < prod.arity(); i++) {
          sbTemp.append("\\exists{");
          convert(sort, sbTemp);
          sbTemp.append("} (X").append(i).append(":");
          convert(prod.nonterminal(i).sort(), prod, sbTemp);
          sbTemp.append(", ");
        }
        convert(prod.klabel().get(), prod, sbTemp);
        sbTemp.append("(");
        String conn = "";
        for (int i = 0; i < prod.arity(); i++) {
          sbTemp.append(conn).append("X").append(i).append(":");
          convert(prod.nonterminal(i).sort(), prod, sbTemp);
          conn = ", ";
        }
        sbTemp.append(")");
        for (int i = 0; i < prod.arity(); i++) {
          sbTemp.append(")");
        }
      }
      sbTemp.append(", ");
    }
    for (Sort s : iterable(module.sortedAllSorts())) {
      if (module.subsorts().lessThan(s, sort) && !sort.equals(Sorts.K())) {
        numTerms++;
        sbTemp.append("\\exists{");
        convert(sort, sbTemp);
        sbTemp.append("} (Val:");
        convert(s, sbTemp);
        sbTemp.append(", inj{");
        convert(s, sbTemp);
        sbTemp.append(", ");
        convert(sort, sbTemp);
        sbTemp.append("} (Val:");
        convert(s, sbTemp);
        sbTemp.append("))");
        sbTemp.append(", ");
      }
    }
    Att sortAtt = module.sortAttributesFor().get(sort.head()).getOrElse(() -> Att.empty());
    if (!hasToken && sortAtt.contains(Att.TOKEN())) {
      numTerms++;
      convertTokenProd(sort, sbTemp);
      sbTemp.append(", ");
      hasToken = true;
    }
    sbTemp.append("\\bottom{");
    convert(sort, sbTemp);
    sbTemp.append("}()) [constructor{}()] // no junk");
    if (hasToken && !METAVAR) {
      sbTemp.append(" (TODO: fix bug with \\dv)");
    }
    sbTemp.append("\n");

    // If there are no terms, then we don't need to generate the axiom.
    if (numTerms != 0) {
      sb.append(sbTemp);
    }
  }

  private void genOverloadedAxiom(Production lesser, Production greater, StringBuilder sb) {
    sb.append("  axiom{R} \\equals{");
    convert(greater.sort(), greater, sb);
    sb.append(", R} (");
    convert(greater.klabel().get(), greater, sb);
    sb.append("(");
    String conn = "";
    for (int i = 0; i < greater.nonterminals().size(); i++) {
      sb.append(conn);
      if (greater.nonterminal(i).sort().equals(lesser.nonterminal(i).sort())) {
        sb.append("K").append(i).append(":");
        convert(greater.nonterminal(i).sort(), greater, sb);
      } else {
        sb.append("inj{");
        convert(lesser.nonterminal(i).sort(), lesser, sb);
        sb.append(", ");
        convert(greater.nonterminal(i).sort(), greater, sb);
        sb.append("} (K").append(i).append(":");
        convert(lesser.nonterminal(i).sort(), lesser, sb);
        sb.append(")");
      }
      conn = ",";
    }

    if (greater.sort().equals(lesser.sort())) {
      sb.append("), ");
    } else {
      sb.append("), inj{");
      convert(lesser.sort(), lesser, sb);
      sb.append(", ");
      convert(greater.sort(), greater, sb);
      sb.append("} (");
    }

    convert(lesser.klabel().get(), lesser, sb);
    sb.append("(");

    conn = "";
    for (int i = 0; i < lesser.nonterminals().size(); i++) {
      sb.append(conn);
      sb.append("K").append(i).append(":");
      convert(lesser.nonterminal(i).sort(), lesser, sb);
      conn = ",";
    }

    if (greater.sort().equals(lesser.sort())) {
      sb.append(")) ");
    } else {
      sb.append("))) ");
    }
    final var args = KList(KApply(greater.klabel().get()), KApply(lesser.klabel().get()));
    final var att = Att.empty().add(Att.SYMBOL_OVERLOAD(), KList.class, args);
    convert(new HashMap<>(), att, sb, null, null);
    sb.append(" // overloaded production\n");
  }

  public String convertSpecificationModule(
      Module definition, Module spec, SentenceType defaultSentenceType, StringBuilder sb) {
    SentenceType sentenceType = getSentenceType(spec.att()).orElse(defaultSentenceType);
    sb.setLength(0); // reset string writer
    Sort topCellSort = Sorts.GeneratedTopCell();
    String topCellSortStr = getSortStr(topCellSort);
    HashMap<Att.Key, Boolean> considerSource = new HashMap<>();
    considerSource.put(Att.SOURCE(), true);
    convert(
        considerSource,
        Att.empty().add(Att.SOURCE(), Source.class, spec.att().get(Att.SOURCE(), Source.class)),
        sb,
        null,
        null);
    sb.append("\n");
    sb.append("module ");
    convert(spec.name(), sb);
    sb.append("\n\n// imports\n");
    sb.append("import ");
    convert(definition.name(), sb);
    sb.append(" []\n");
    sb.append("\n\n// claims\n");
    HashMap<Att.Key, Boolean> consideredAttributes = new HashMap<>();
    consideredAttributes.put(Att.PRIORITY(), true);
    consideredAttributes.put(Att.LABEL(), true);
    consideredAttributes.put(Att.GROUP(), true);
    consideredAttributes.put(Att.SOURCE(), true);
    consideredAttributes.put(Att.LOCATION(), true);
    consideredAttributes.put(Att.UNIQUE_ID(), true);

    for (Sentence sentence : iterable(spec.sentencesExcept(definition))) {
      if (sentence instanceof Claim
          || (sentence instanceof Rule && sentence.att().contains(Att.SIMPLIFICATION()))) {
        convertRule(
            (RuleOrClaim) sentence,
            0,
            false,
            topCellSortStr,
            consideredAttributes,
            HashMultimap.create(),
            new HashMap<>(),
            ArrayListMultimap.create(),
            sentenceType,
            sb);
      }
    }
    sb.append("endmodule ");
    convert(consideredAttributes, spec.att().remove(Att.DIGEST()), sb, null, null);
    sb.append("\n");
    return sb.toString();
  }

  private Optional<SentenceType> getSentenceType(Att att) {
    if (att.contains(Att.ONE_PATH())) {
      return Optional.of(SentenceType.ONE_PATH);
    } else if (att.contains(Att.ALL_PATH())) {
      return Optional.of(SentenceType.ALL_PATH);
    }
    return Optional.empty();
  }

  private RuleInfo getRuleInfo(RuleOrClaim rule, boolean heatCoolEq, String topCellSortStr) {
    boolean equation = false;
    boolean owise = false;
    boolean ceil = false;
    Production production = null;
    Sort productionSort = null;
    String productionSortStr = null;
    List<Sort> productionSorts = null;
    KLabel productionLabel = null;
    List<K> leftChildren = null;

    K left = RewriteToTop.toLeft(rule.body());
    K leftPattern = left;
    while (leftPattern instanceof KAs) {
      leftPattern = ((KAs) leftPattern).pattern();
    }
    if (leftPattern instanceof KApply) {
      production = production((KApply) leftPattern, true);
      productionSort = production.sort();
      productionSortStr = getSortStr(productionSort);
      productionSorts =
          stream(production.items())
              .filter(i -> i instanceof NonTerminal)
              .map(i -> (NonTerminal) i)
              .map(NonTerminal::sort)
              .collect(Collectors.toList());
      productionLabel = production.klabel().get();
      if (productionLabel.name().equals("#Ceil") && rule.att().contains(Att.SIMPLIFICATION())) {
        ceil = true;
      }
      if (isFunction(production)
          || rule.att().contains(Att.SIMPLIFICATION())
          || rule.att().contains(Att.ANYWHERE())) {
        leftChildren = ((KApply) leftPattern).items();
        equation = true;
      } else if ((rule.att().contains(Att.HEAT()) || rule.att().contains(Att.COOL()))
          && heatCoolEq) {
        equation = true;
        productionSortStr = topCellSortStr;
      }
      owise = rule.att().contains(Att.OWISE());
    } else if (leftPattern instanceof KToken kt) {
      productionSort = kt.sort();
      productionSortStr = getSortStr(productionSort);
    }

    return new RuleInfo(
        equation,
        owise,
        ceil,
        production,
        productionSortStr,
        productionSorts,
        productionLabel,
        leftChildren);
  }

  private void convertRule(
      RuleOrClaim rule,
      int ruleIndex,
      boolean heatCoolEq,
      String topCellSortStr,
      Map<Att.Key, Boolean> consideredAttributes,
      SetMultimap<KLabel, Rule> functionRules,
      Map<Integer, String> priorityToPreviousGroup,
      ListMultimap<Integer, String> priorityToAlias,
      SentenceType defaultSentenceType,
      StringBuilder sb) {
    SentenceType sentenceType = getSentenceType(rule.att()).orElse(defaultSentenceType);
    // injections should already be present, but this is an ugly hack to get around the
    // cache persistence issue that means that Sort attributes on k terms might not be present.
    rule = addSortInjections.addInjections(rule);
    Set<KVariable> existentials = getExistentials(rule);
    ConstructorChecks constructorChecks = new ConstructorChecks(module);
    K left = RewriteToTop.toLeft(rule.body());
    K requires = rule.requires();
    K right = RewriteToTop.toRight(rule.body());
    K ensures = rule.ensures();
    boolean constructorBased = constructorChecks.isConstructorBased(left);
    RuleInfo ruleInfo = getRuleInfo(rule, heatCoolEq, topCellSortStr);
    sb.append("// ");
    sb.append(rule);
    sb.append("\n");
    if (ruleInfo.isCeil && options.disableCeilSimplificationRules) {
      return;
    }
    Set<KVariable> freeVariables = collectLHSFreeVariables(requires, left);
    Map<String, KVariable> freeVarsMap =
        freeVariables.stream().collect(Collectors.toMap(KVariable::name, Function.identity()));
    if (ruleInfo.isEquation) {
      assertNoExistentials(rule, existentials);
      if (rule instanceof Claim) {
        sb.append("  claim{R");
        if (!allowFuncClaims) // TODO: remove once
          // https://github.com/runtimeverification/haskell-backend/issues/3010 is
          // implemented
          kem.registerCompilerWarning(
              KException.ExceptionType.FUTURE_ERROR,
              "Functional claims not yet supported."
                  + " https://github.com/runtimeverification/haskell-backend/issues/3010",
              rule);
      } else {
        sb.append("  axiom{R");
      }
      Option<Sort> sortParamsWrapper = rule.att().getOption(Att.SORT_PARAMS(), Sort.class);
      Option<Set<String>> sortParams =
          sortParamsWrapper.map(
              s -> stream(s.params()).map(sort -> sort.name()).collect(Collectors.toSet()));
      if (sortParams.nonEmpty()) {
        for (Object sortParamName : sortParams.get()) sb.append("," + sortParamName);
      }
      sb.append("} ");
      if (ruleInfo.isOwise) {
        Set<String> varNames =
            freeVariables.stream().map(KVariable::name).collect(Collectors.toSet());
        sb.append("\\implies{R} (\n    \\and{R} (\n      \\not{R} (\n        ");
        for (Rule notMatching :
            RefreshRules.refresh(functionRules.get(ruleInfo.productionLabel), varNames)) {
          if (ignoreSideConditionsForOwise(notMatching)) {
            continue;
          }
          sb.append("\\or{R} (\n");
          K notMatchingRequires = notMatching.requires();
          K notMatchingLeft = RewriteToTop.toLeft(notMatching.body());
          Set<KVariable> vars = collectLHSFreeVariables(notMatchingRequires, notMatchingLeft);
          sb.append("          ");
          for (KVariable var : vars) {
            sb.append("\\exists{R} (");
            convert((K) var, sb);
            sb.append(",\n          ");
          }
          sb.append("  \\and{R} (");
          sb.append("\n              ");
          convertSideCondition(notMatchingRequires, sb);
          sb.append(",\n              ");

          assert notMatchingLeft instanceof KApply
              : "expecting KApply but got " + notMatchingLeft.getClass();
          List<K> notMatchingChildren = ((KApply) notMatchingLeft).items();
          assert notMatchingChildren.size() == ruleInfo.leftChildren.size()
              : "assuming function with fixed arity";
          for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
            sb.append("\\and{R} (");
            sb.append("\n                ");
            sb.append("\\in{");
            Sort childSort = ruleInfo.prodChildrenSorts.get(childIdx);
            convert(childSort, ruleInfo.production.params(), sb);
            sb.append(", R} (");
            sb.append("\n                  ");
            sb.append("X").append(childIdx).append(":");
            convert(childSort, ruleInfo.production.params(), sb);
            sb.append(",\n                  ");
            convert(notMatchingChildren.get(childIdx), sb);
            sb.append("\n                ),");
          }
          sb.append("\n                \\top{R} ()");
          sb.append("\n              ");
          for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
            sb.append(')');
          }
          sb.append("\n          )");
          for (KVariable ignored : vars) {
            sb.append(")");
          }
          sb.append(",\n          ");
        }
        sb.append("\\bottom{R}()");
        sb.append("\n        ");
        for (Rule notMatching : functionRules.get(ruleInfo.productionLabel)) {
          if (ignoreSideConditionsForOwise(notMatching)) {
            continue;
          }
          sb.append(")");
        }
        sb.append("\n      ),\n      \\and{R}(\n        ");
        convertSideCondition(requires, sb);
        sb.append(",\n        ");

        for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
          sb.append("\\and{R} (");
          sb.append("\n          ");
          sb.append("\\in{");
          Sort childSort = ruleInfo.prodChildrenSorts.get(childIdx);
          convert(childSort, ruleInfo.production.params(), sb);
          sb.append(", R} (");
          sb.append("\n            ");
          sb.append("X").append(childIdx).append(":");
          convert(childSort, ruleInfo.production.params(), sb);
          sb.append(",\n            ");
          convert(ruleInfo.leftChildren.get(childIdx), sb);
          sb.append("\n          ),");
        }
        sb.append("\n          \\top{R} ()");
        sb.append("\n        ");
        for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
          sb.append(')');
        }

        sb.append("\n    )),\n    \\equals{");
        sb.append(ruleInfo.productionSortStr);
        sb.append(",R} (\n      ");
        convert(ruleInfo.productionLabel, sb);
        sb.append("(");
        String conn = "";
        for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
          sb.append(conn).append("X").append(childIdx).append(":");
          Sort childSort = ruleInfo.prodChildrenSorts.get(childIdx);
          convert(childSort, ruleInfo.production.params(), sb);
          conn = ",";
        }
        sb.append(")");
        sb.append(",\n     \\and{");
        sb.append(ruleInfo.productionSortStr);
        sb.append("} (\n       ");
        convert(right, sb);
        sb.append(",\n        ");
        convertSideCondition(ensures, ruleInfo.productionSortStr, sb);
        sb.append(")))\n  ");
        convert(consideredAttributes, rule.att(), sb, freeVarsMap, rule);
        sb.append("\n\n");
      } else if (rule.att().contains(Att.SIMPLIFICATION()) || rule instanceof Claim) {
        sb.append("\\implies{R} (\n    ");
        convertSideCondition(requires, sb);
        sb.append(",\n    \\equals{");
        sb.append(ruleInfo.productionSortStr);
        sb.append(",R} (\n      ");
        convert(left, sb);
        sb.append(",\n     \\and{");
        sb.append(ruleInfo.productionSortStr);
        sb.append("} (\n       ");
        convert(right, sb);
        sb.append(",\n        ");
        convertSideCondition(ensures, ruleInfo.productionSortStr, sb);
        sb.append(")))\n  ");
        convert(consideredAttributes, rule.att(), sb, freeVarsMap, rule);
        sb.append("\n\n");

      } else {
        sb.append("\\implies{R} (\n    \\and{R}(\n      ");
        convertSideCondition(requires, sb);
        sb.append(",\n      ");

        for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
          sb.append("\\and{R} (");
          sb.append("\n          ");
          sb.append("\\in{");
          Sort childSort = ruleInfo.prodChildrenSorts.get(childIdx);
          convert(childSort, ruleInfo.production.params(), sb);
          sb.append(", R} (");
          sb.append("\n            ");
          sb.append("X").append(childIdx).append(":");
          convert(childSort, ruleInfo.production.params(), sb);
          sb.append(",\n            ");
          convert(ruleInfo.leftChildren.get(childIdx), sb);
          sb.append("\n          ),");
        }
        sb.append("\n          \\top{R} ()");
        sb.append("\n        ");
        for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
          sb.append(')');
        }
        sb.append("),\n    \\equals{");
        sb.append(ruleInfo.productionSortStr);
        sb.append(",R} (\n      ");
        convert(ruleInfo.productionLabel, sb);
        sb.append("(");
        String conn = "";
        for (int childIdx = 0; childIdx < ruleInfo.leftChildren.size(); childIdx++) {
          sb.append(conn).append("X").append(childIdx).append(":");
          Sort childSort = ruleInfo.prodChildrenSorts.get(childIdx);
          convert(childSort, ruleInfo.production.params(), sb);
          conn = ",";
        }
        sb.append(")");
        sb.append(",\n     \\and{");
        sb.append(ruleInfo.productionSortStr);
        sb.append("} (\n       ");
        convert(right, sb);
        sb.append(",\n        ");
        convertSideCondition(ensures, ruleInfo.productionSortStr, sb);
        sb.append(")))\n  ");
        convert(consideredAttributes, rule.att(), sb, freeVarsMap, rule);
        sb.append("\n\n");
      }
    } else if (!ExpandMacros.isMacro(rule)) {
      // generate rule LHS
      if (!(rule instanceof Claim)) {
        // LHS for semantics rules
        String ruleAliasName = String.format("rule%dLHS", ruleIndex);
        int priority = getPriority(rule.att());
        List<KVariable> freeVars = new ArrayList<>(freeVariables);
        Comparator<KVariable> compareByName =
            (KVariable v1, KVariable v2) -> v1.name().compareTo(v2.name());
        java.util.Collections.sort(freeVars, compareByName);

        if (options.enableKoreAntileft) {
          genAliasForSemanticsRuleLHS(
              requires,
              left,
              ruleAliasName,
              freeVars,
              topCellSortStr,
              priority,
              priorityToAlias,
              sb);
          sb.append("\n");
        }

        sb.append("  axiom{} ");
        sb.append(String.format("\\rewrites{%s} (\n    ", topCellSortStr));

        if (options.enableKoreAntileft) {
          genSemanticsRuleLHSWithAlias(
              ruleAliasName, freeVars, topCellSortStr, priorityToPreviousGroup.get(priority), sb);
          sb.append(",\n    ");
        } else {
          genSemanticsRuleLHSNoAlias(
              requires, left, freeVars, topCellSortStr, priorityToPreviousGroup.get(priority), sb);
          sb.append(",\n      ");
        }
      } else {
        // LHS for claims
        sb.append("  claim{} ");
        sb.append(String.format("\\implies{%s} (\n    ", ruleInfo.productionSortStr));
        sb.append(String.format("  \\and{%s} (\n      ", ruleInfo.productionSortStr));
        convertSideCondition(requires, ruleInfo.productionSortStr, sb);
        sb.append(", ");
        convert(left, sb);
        sb.append("), ");
      }

      // generate rule RHS
      if (sentenceType == SentenceType.ALL_PATH) {
        sb.append(String.format("%s{%s} (\n      ", ALL_PATH_OP, ruleInfo.productionSortStr));
      } else if (sentenceType == SentenceType.ONE_PATH) {
        sb.append(String.format("%s{%s} (\n      ", ONE_PATH_OP, ruleInfo.productionSortStr));
      }
      if (!existentials.isEmpty()) {
        for (KVariable exists : existentials) {
          sb.append(String.format(" \\exists{%s} (", ruleInfo.productionSortStr));
          convert((K) exists, sb);
          sb.append(", ");
        }
        sb.append("\n      ");
      }
      sb.append(String.format("\\and{%s} (\n      ", ruleInfo.productionSortStr));

      if (options.enableKoreAntileft) {
        convertSideCondition(ensures, ruleInfo.productionSortStr, sb);
        sb.append(", ");
        convert(right, sb);
      } else {
        convert(right, sb);
        sb.append(", ");
        convertSideCondition(ensures, ruleInfo.productionSortStr, sb);
      }

      sb.append(')');
      for (KVariable ignored : existentials) {
        sb.append(')');
      }
      if (rule instanceof Claim) {
        sb.append(')');
      }
      sb.append(')');
      sb.append("\n  ");
      convert(consideredAttributes, rule.att(), sb, freeVarsMap, rule);
      sb.append("\n\n");
    } else {
      assertNoExistentials(rule, existentials);
      sb.append("  axiom{R");
      Option<Sort> sortParamsWrapper = rule.att().getOption(Att.SORT_PARAMS(), Sort.class);
      Option<Set<String>> sortParams =
          sortParamsWrapper.map(
              s -> stream(s.params()).map(sort -> sort.name()).collect(Collectors.toSet()));
      if (sortParams.nonEmpty()) {
        for (Object sortParamName : sortParams.get()) sb.append("," + sortParamName);
      }
      sb.append("} ");
      sb.append("\\equals{");
      sb.append(ruleInfo.productionSortStr);
      sb.append(",R} (\n    ");
      convert(left, sb);
      sb.append(",\n    ");
      convert(right, sb);
      sb.append(")\n  ");
      convert(
          consideredAttributes,
          rule.att().add(Att.PRIORITY(), Integer.toString(getPriority(rule.att()))),
          sb,
          freeVarsMap,
          rule);
      sb.append("\n\n");
    }
  }

  private boolean ignoreSideConditionsForOwise(Rule notMatching) {
    return notMatching.att().contains(Att.OWISE())
        || notMatching.att().contains(Att.SIMPLIFICATION())
        || notMatching.att().contains(Att.NON_EXECUTABLE());
  }

  private void assertNoExistentials(Sentence sentence, Set<KVariable> existentials) {
    if (!existentials.isEmpty()) {
      throw KEMException.compilerError(
          "Cannot encode equations with existential variables to KORE."
              + "\n If this is desired, please use #Exists with regular variables."
              + "\n Offending variables: "
              + existentials
              + "\n context: "
              + sentence);
    }
  }

  private Set<KVariable> getExistentials(RuleOrClaim rule) {
    Set<KVariable> res = new HashSet<>();
    VisitK visitor =
        new VisitK() {
          @Override
          public void apply(KVariable k) {
            if (k.name().startsWith("?") || k.att().contains(Att.FRESH())) res.add(k);
          }
        };
    visitor.apply(rule.ensures());
    visitor.apply(RewriteToTop.toRight(rule.body()));
    return res;
  }

  private void genAliasForSemanticsRuleLHS(
      K requires,
      K left,
      String ruleAliasName,
      List<KVariable> freeVars,
      String topCellSortStr,
      Integer priority,
      ListMultimap<Integer, String> priorityToAlias,
      StringBuilder sb) {
    sb.append("  alias ");
    sb.append(ruleAliasName);
    // We assume no sort variables.
    sb.append("{}(");
    String conn = "";
    for (KVariable var : freeVars) {
      sb.append(conn);
      convert(var.att().getOptional(Att.SORT(), Sort.class).orElse(Sorts.K()), sb);
      conn = ",";
    }
    sb.append(") : ");
    sb.append(topCellSortStr);
    sb.append("\n  where ");
    genAliasDeclHead(ruleAliasName, freeVars, sb);
    sb.append(") :=\n");
    sb.append(String.format("    \\and{%s} (\n      ", topCellSortStr));
    convertSideCondition(requires, topCellSortStr, sb);
    sb.append(", ");
    convert(left, sb);
    sb.append(") []\n");

    // build existential quantified pattern for alias
    StringBuilder extStrBuilder = new StringBuilder();
    for (KVariable var : freeVars) {
      extStrBuilder.append(String.format("\\exists{%s}(", topCellSortStr));
      convert((K) var, extStrBuilder);
      extStrBuilder.append(",");
    }
    genAliasDeclHead(ruleAliasName, freeVars, extStrBuilder);
    extStrBuilder.append(")");
    for (int i = 0; i < freeVars.size(); i++) {
      extStrBuilder.append(")");
    }
    priorityToAlias.put(priority, extStrBuilder.toString());
  }

  private void genAliasDeclHead(String aliasName, List<KVariable> freeVars, StringBuilder sb) {
    sb.append(aliasName);
    sb.append("{}(");
    String conn = "";
    for (KVariable var : freeVars) {
      sb.append(conn);
      convert((K) var, sb);
      conn = ",";
    }
  }

  private void genSemanticsRuleLHSWithAlias(
      String ruleAliasName,
      List<KVariable> freeVars,
      String topCellSortStr,
      String previousGroupName,
      StringBuilder sb) {
    if (!previousGroupName.equals("")) {
      sb.append(String.format("\\and{%s}(\n      ", topCellSortStr));
      sb.append(String.format("\\not{%s}(", topCellSortStr));
      sb.append(previousGroupName);
      sb.append("{}()),\n      ");
    }
    sb.append(ruleAliasName);
    sb.append("{}(");
    String conn = "";
    for (KVariable var : freeVars) {
      sb.append(conn);
      convert((K) var, sb);
      conn = ",";
    }
    sb.append(")");
    if (!previousGroupName.equals("")) {
      sb.append(")");
    }
  }

  private void genSemanticsRuleLHSNoAlias(
      K requires,
      K left,
      List<KVariable> freeVars,
      String topCellSortStr,
      String previousGroupName,
      StringBuilder sb) {
    sb.append(String.format("  \\and{%s} (\n        ", topCellSortStr));
    convert(left, sb);
    sb.append(",\n        ");
    convertSideCondition(requires, topCellSortStr, sb);
    sb.append(")");
  }

  private void genPriorityGroups(
      List<Integer> priorityList,
      Map<Integer, String> priorityToPreviousGroup,
      ListMultimap<Integer, String> priorityToAlias,
      String topCellSortStr,
      StringBuilder sb) {
    // skip generating alias for the last priority group
    for (int index = 0; index < priorityList.size() - 1; index++) {
      Integer priority = priorityList.get(index);
      String priorityGroupName = String.format("priorityLE%d", priority);
      sb.append(String.format("  alias %s{}() : %s", priorityGroupName, topCellSortStr));
      sb.append(String.format("\n  where %s{}() := ", priorityGroupName));
      String previousGroupName = priorityToPreviousGroup.get(priority);
      if (!previousGroupName.equals("")) {
        sb.append(String.format("\\or{%s}(\n    ", topCellSortStr));
        sb.append(previousGroupName);
        sb.append("{}(), ");
      }
      // generate priority group body
      List<String> aliases = priorityToAlias.get(priority);
      for (String ruleLHSAlias : aliases) {
        sb.append(String.format("\\or{%s}(\n    ", topCellSortStr));
        sb.append(ruleLHSAlias);
        sb.append(", ");
      }
      // bottom is the unit of "or"
      sb.append(String.format("\\bottom{%s}()", topCellSortStr));
      // complete parenthesis
      for (int i = 0; i < aliases.size(); i++) {
        sb.append(")");
      }
      if (!previousGroupName.equals("")) {
        sb.append(")");
      }
      sb.append(" []\n\n");
    }
  }

  private void functionalPattern(Production prod, Runnable functionPattern, StringBuilder sb) {
    sb.append("  axiom");
    convertParams(prod.klabel(), true, sb);
    sb.append(" \\exists{R} (Val:");
    convert(prod.sort(), prod, sb);
    sb.append(", \\equals{");
    convert(prod.sort(), prod, sb);
    sb.append(", R} (");
    sb.append("Val:");
    convert(prod.sort(), prod, sb);
    sb.append(", ");
    functionPattern.run();
    sb.append("))");
  }

  private void applyPattern(Production prod, String varName, StringBuilder sb) {
    convert(prod.klabel().get(), prod, sb);
    sb.append("(");
    String conn = "";
    for (int i = 0; i < prod.arity(); i++) {
      sb.append(conn);
      sb.append(varName).append(i).append(":");
      convert(prod.nonterminal(i).sort(), prod, sb);
      conn = ", ";
    }
    sb.append(')');
  }

  private void convertTokenProd(Sort sort, StringBuilder sb) {
    if (METAVAR) {
      sb.append("\\exists{");
      convert(sort, sb);
      sb.append("} (#Str:#String{}, \\dv{");
      convert(sort, sb);
      sb.append("}(#Str:#String{}))");
    } else {
      sb.append("\\top{");
      convert(sort, sb);
      sb.append("}()");
    }
  }

  private void convertParams(Option<KLabel> maybeKLabel, boolean hasR, StringBuilder sb) {
    sb.append("{");
    String conn = "";
    if (hasR) {
      sb.append("R");
      if (maybeKLabel.isDefined()) {
        conn = ", ";
      }
    }
    if (maybeKLabel.isDefined()) {
      for (Sort param : iterable(maybeKLabel.get().params())) {
        sb.append(conn);
        convert(param, Seq(param), sb);
        conn = ", ";
      }
    }
    sb.append("}");
  }

  private boolean isConstructor(
      Production prod, SetMultimap<KLabel, Rule> functionRules, Set<KLabel> impurities) {
    Att att = semanticAttributes(prod, functionRules, impurities, java.util.Collections.emptySet());
    return att.contains(Att.CONSTRUCTOR());
  }

  private static boolean isFunctional(Production prod) {
    return !isFunction(prod) || prod.att().contains(Att.TOTAL());
  }

  private static boolean isFunction(Production prod) {
    return prod.att().contains(Att.FUNCTION());
  }

  private boolean isHook(Production prod) {
    return prod.att().contains(Att.HOOK()) && isRealHook(prod.att());
  }

  private boolean isRealHook(Att att) {
    String hook = att.get(Att.HOOK());
    return Stream.concat(Hooks.namespaces.stream(), options.hookNamespaces.stream())
        .anyMatch(ns -> hook.startsWith(ns + "."));
  }

  private static boolean isBuiltinProduction(Production prod) {
    return prod.klabel().nonEmpty() && ConstructorChecks.isBuiltinLabel(prod.klabel().get());
  }

  private boolean isGeneratedInKeysOp(Production prod) {
    Option<String> hook = prod.att().getOption(Att.HOOK());
    if (hook.isEmpty()) return false;
    if (!hook.get().equals("MAP.in_keys")) return false;
    return (!prod.klabel().isEmpty());
  }

  private Att koreAttributes(
      Production prod,
      SetMultimap<KLabel, Rule> functionRules,
      Set<KLabel> impurities,
      Set<Production> overloads,
      boolean withSyntaxAtts) {
    Att att = prod.att();
    List<Att.Key> attsToRemove =
        List.of(
            // semantics
            Att.CONSTRUCTOR(),
            Att.HOOK(),
            // syntax
            Att.ASSOC(),
            Att.BRACKET(),
            Att.COLORS(),
            Att.COMM(),
            Att.FORMAT());
    for (Att.Key key : attsToRemove) {
      att = att.remove(key);
    }
    att = att.addAll(semanticAttributes(prod, functionRules, impurities, overloads));
    if (withSyntaxAtts) {
      att = att.addAll(syntaxAttributes(prod));
    }
    return att;
  }

  private Att semanticAttributes(
      Production prod,
      SetMultimap<KLabel, Rule> functionRules,
      Set<KLabel> impurities,
      Set<Production> overloads) {
    boolean isConstructor = !isFunction(prod);
    isConstructor &= !prod.att().contains(Att.ASSOC());
    isConstructor &= !prod.att().contains(Att.COMM());
    isConstructor &= !prod.att().contains(Att.IDEM());
    isConstructor &= !(prod.att().contains(Att.FUNCTION()) && prod.att().contains(Att.UNIT()));

    // Later we might set !isConstructor because there are anywhere rules,
    // but if a symbol is a constructor at this point, then it is still
    // injective.
    boolean isInjective = isConstructor;

    boolean isMacro = prod.isMacro();
    boolean isAnywhere = overloads.contains(prod);

    Att att = Att.empty();

    if (prod.klabel().isDefined()) {
      for (Rule r : functionRules.get(prod.klabel().get())) {
        isAnywhere |= r.att().contains(Att.ANYWHERE());
      }
      if (impurities.contains(prod.klabel().get())) {
        att = att.add(Att.IMPURE());
      }
    }

    isConstructor &= !isMacro;
    isConstructor &= !isAnywhere;

    if (isHook(prod)) {
      att = att.add(Att.HOOK(), prod.att().get(att.HOOK()));
    }
    if (isConstructor) {
      att = att.add(Att.CONSTRUCTOR());
    }
    if (isFunctional(prod)) {
      att = att.add(Att.FUNCTIONAL());
    }
    if (isAnywhere) {
      att = att.add(Att.ANYWHERE());
    }
    if (isInjective) {
      att = att.add(Att.INJECTIVE());
    }
    if (isMacro) {
      att = att.add(Att.MACRO());
    }
    return att;
  }

  private Att syntaxAttributes(Production prod) {
    // update format attribute with structure expected by backend
    String format = prod.att().getOptional(Att.FORMAT()).orElse(prod.defaultFormat());
    int nt = 1;

    for (int i = 0; i < prod.items().size(); i++) {
      if (prod.items().apply(i) instanceof NonTerminal) {
        String replacement = "%" + (nt++);
        format = format.replaceAll("%" + (i + 1) + "(?![0-9])", replacement);
      } else if (prod.items().apply(i) instanceof Terminal) {
        format =
            format.replaceAll(
                "%" + (i + 1) + "(?![0-9])",
                "%c"
                    + ((Terminal) prod.items().apply(i))
                        .value()
                        .replace("\\", "\\\\")
                        .replace("$", "\\$")
                        .replace("%", "%%")
                    + "%r");
      } else {
        return Att.empty();
      }
    }

    Att att = Att.empty();
    att = att.add(Att.FORMAT(), format);

    List<Att.Key> attsToCopy = List.of(Att.ASSOC(), Att.BRACKET(), Att.COLORS(), Att.COMM());
    for (Att.Key key : attsToCopy) {
      if (prod.att().contains(key)) {
        att = att.add(key, prod.att().get(key));
      }
    }

    if (prod.att().contains(Att.COLOR())) {
      String color = prod.att().get(Att.COLOR());
      boolean escape = false;
      StringBuilder colors = new StringBuilder();
      String conn = "";
      for (int i = 0; i < format.length(); i++) {
        if (escape && format.charAt(i) == 'c') {
          colors.append(conn).append(color);
          conn = ",";
        }
        escape = format.charAt(i) == '%';
      }
      att = att.add(Att.COLORS(), colors.toString());
    }
    StringBuilder sb = new StringBuilder();
    for (ProductionItem pi : iterable(prod.items())) {
      if (pi instanceof NonTerminal) {
        sb.append('0');
      } else {
        sb.append('1');
      }
    }
    att = att.add(Att.TERMINALS(), sb.toString());
    if (prod.klabel().isDefined()) {
      att = att.add(Att.PRIORITIES(), KList.class, getPriorities(prod.klabel().get()));
      att =
          att.add(
              Att.LEFT_INTERNAL(), KList.class, getAssoc(module.leftAssoc(), prod.klabel().get()));
      att =
          att.add(
              Att.RIGHT_INTERNAL(),
              KList.class,
              getAssoc(module.rightAssoc(), prod.klabel().get()));
    }
    return att;
  }

  private KList getPriorities(KLabel klabel) {
    List<String> tags = new ArrayList<>();
    Optional<Set<Tag>> lessThan =
        Optional.ofNullable(module.priorities().relations().get(Tag(klabel.name())));
    if (lessThan.isPresent()) {
      for (Tag tag : lessThan.get()) {
        if (ConstructorChecks.isBuiltinLabel(KLabel(tag.name()))) {
          continue;
        }
        tags.add(tag.name());
      }
    }
    return KList(
        tags.stream()
            .sorted(Comparator.naturalOrder())
            .map(tag -> KApply(KLabel(tag)))
            .collect(Collectors.toList()));
  }

  private KList getAssoc(scala.collection.Set<Tuple2<Tag, Tag>> assoc, KLabel klabel) {
    return KList(
        stream(assoc)
            .filter(t -> t._1().name().equals(klabel.name()))
            .sorted(Comparator.comparing(t -> t._2().name()))
            .map(t -> KApply(KLabel(t._2().name())))
            .collect(Collectors.toList()));
  }

  // Assume that there is no quantifiers
  private Set<KVariable> collectLHSFreeVariables(K requires, K left) {
    Set<KVariable> res = new HashSet<>();
    VisitK visitor =
        new VisitK() {
          @Override
          public void apply(KVariable k) {
            res.add(k);
          }
        };
    visitor.apply(requires);
    visitor.apply(left);
    return res;
  }

  private void convertSideCondition(K k, StringBuilder sb) {
    if (k.equals(BooleanUtils.TRUE)) {
      sb.append("\\top{R}()");
    } else {
      sb.append("\\equals{SortBool{},R}(\n        ");
      convert(k, sb);
      sb.append(",\n        \\dv{SortBool{}}(\"true\"))");
    }
  }

  private void convertSideCondition(K k, String resultSortStr, StringBuilder sb) {
    if (k.equals(BooleanUtils.TRUE)) {
      sb.append(String.format("\\top{%s}()", resultSortStr));
    } else {
      sb.append(String.format("\\equals{SortBool{},%s}(\n        ", resultSortStr));
      convert(k, sb);
      sb.append(",\n        \\dv{SortBool{}}(\"true\"))");
    }
  }

  private KLabel computePolyKLabel(KApply k) {
    String labelName = k.klabel().name();
    if (mlBinders.contains(
        labelName)) { // ML binders are not parametric in the variable so we remove it
      List<Sort> params = mutable(k.klabel().params());
      if (!params.isEmpty()) {
        params.remove(0);
      }
      return KLabel(labelName, immutable(params));
    } else {
      return k.klabel();
    }
  }

  private void collectAttributes(Map<Att.Key, Boolean> attributes, Att att) {
    for (Tuple2<Tuple2<Att.Key, String>, ?> attribute : iterable(att.att())) {
      Att.Key name = attribute._1._1;
      Object val = attribute._2;
      String strVal = val.toString();
      if (strVal.equals("")) {
        if (!attributes.containsKey(name)) {
          attributes.put(name, false);
        }
      } else {
        attributes.put(name, true);
      }
    }
  }

  private static final Production INJ_PROD =
      Production(
          KLabel(KLabels.INJ, Sort("S1"), Sort("S2")),
          Sort("S2"),
          Seq(NonTerminal(Sort("S1"))),
          Att.empty());

  private Production production(KApply term) {
    return production(term, false);
  }

  private Production production(KApply term, boolean instantiatePolySorts) {
    KLabel klabel = term.klabel();
    if (klabel.name().equals(KLabels.INJ))
      return instantiatePolySorts ? INJ_PROD.substitute(term.klabel().params()) : INJ_PROD;
    Option<scala.collection.immutable.Set<Production>> prods =
        module.productionsFor().get(klabel.head());
    if (!(prods.nonEmpty() && prods.get().size() == 1))
      throw KEMException.compilerError(
          "Expected to find exactly one production for KLabel: "
              + klabel
              + " found: "
              + prods.getOrElse(Collections::Set).size());
    return instantiatePolySorts
        ? prods.get().head().substitute(term.klabel().params())
        : prods.get().head();
  }

  private static String convertBuiltinLabel(String klabel) {
    return switch (klabel) {
      case "#Bottom" -> "\\bottom";
      case "#Top" -> "\\top";
      case "#Or" -> "\\or";
      case "#And" -> "\\and";
      case "#Not" -> "\\not";
      case "#Floor" -> "\\floor";
      case "#Ceil" -> "\\ceil";
      case "#Equals" -> "\\equals";
      case "#Implies" -> "\\implies";
      case "#Exists" -> "\\exists";
      case "#Forall" -> "\\forall";
      case "#AG" -> "allPathGlobally";
      case "weakExistsFinally" -> ONE_PATH_OP;
      case "weakAlwaysFinally" -> ALL_PATH_OP;
      default -> throw KEMException.compilerError("Unsuppored kore connective in rule: " + klabel);
    };
  }

  public static void convert(KLabel klabel, StringBuilder sb) {
    convert(klabel, java.util.Collections.emptySet(), sb);
  }

  private void convert(
      KLabel klabel, scala.collection.immutable.Seq<Sort> params, StringBuilder sb) {
    convert(klabel, mutable(params), sb);
  }

  private static void convert(KLabel klabel, Collection<Sort> params, StringBuilder sb) {
    if (klabel.name().equals(KLabels.INJ)) {
      sb.append(klabel.name());
    } else if (ConstructorChecks.isBuiltinLabel(klabel)) {
      sb.append(convertBuiltinLabel(klabel.name()));
    } else {
      sb.append("Lbl");
      convert(klabel.name(), sb);
    }
    sb.append("{");
    String conn = "";
    for (Sort param : iterable(klabel.params())) {
      sb.append(conn);
      convert(param, params, sb);
      conn = ", ";
    }
    sb.append("}");
  }

  private void convert(KLabel klabel, Production prod, StringBuilder sb) {
    if (klabel.name().equals(KLabels.INJ)) {
      sb.append(klabel.name());
    } else {
      sb.append("Lbl");
      convert(klabel.name(), sb);
    }
    sb.append("{");
    String conn = "";
    for (Sort param : iterable(klabel.params())) {
      sb.append(conn);
      convert(param, prod, sb);
      conn = ", ";
    }
    sb.append("}");
  }

  private void convert(Sort sort, Production prod, StringBuilder sb) {
    convert(sort, prod.params(), sb);
  }

  public static void convert(Sort sort, StringBuilder sb) {
    convert(sort, java.util.Collections.emptySet(), sb);
  }

  private void convert(SortHead sort, StringBuilder sb) {
    List<Sort> params = new ArrayList<>();
    for (int i = 0; i < sort.params(); i++) {
      params.add(Sort("S" + i));
    }
    convert(Sort(sort.name(), immutable(params)), params, sb);
  }

  private void convert(Sort sort, scala.collection.immutable.Seq<Sort> params, StringBuilder sb) {
    convert(sort, mutable(params), sb);
  }

  private static void convert(Sort sort, Collection<Sort> params, StringBuilder sb) {
    if (sort.name().equals(AddSortInjections.SORTPARAM_NAME)) {
      String sortVar = sort.params().headOption().get().name();
      sb.append(sortVar);
      return;
    }
    sb.append("Sort");
    convert(sort.name(), sb);
    if (!params.contains(sort)) {
      sb.append("{");
      String conn = "";
      for (Sort param : iterable(sort.params())) {
        sb.append(conn);
        convert(param, params, sb);
        conn = ", ";
      }
      sb.append("}");
    }
  }

  private String getSortStr(Sort sort) {
    StringBuilder strBuilder = new StringBuilder();
    convert(sort, strBuilder);
    return strBuilder.toString();
  }

  private void convert(
      Map<Att.Key, Boolean> attributes,
      Att att,
      StringBuilder sb,
      Map<String, KVariable> freeVarsMap,
      HasLocation location) {
    sb.append("[");
    String conn = "";

    for (Tuple2<Tuple2<Att.Key, String>, ?> attribute :
        // Sort to stabilize error messages
        stream(att.att())
            .filter(e -> e._1._1.shouldEmit())
            .sorted(Comparator.comparing(Tuple2::toString))
            .toList()) {
      Att.Key key = attribute._1._1;
      String strKey = key.key();
      String clsName = attribute._1._2;
      Object val = attribute._2;
      String strVal = val.toString();
      sb.append(conn);
      if (clsName.equals(K.class.getName())) {
        convert(strKey, sb);
        sb.append("{}(");
        convert((K) val, sb);
        sb.append(")");
      } else if (clsName.equals(KList.class.getName())) {
        convert(strKey, sb);
        sb.append("{}(");
        String conn2 = "";
        for (K item : ((KList) val).items()) {
          sb.append(conn2);
          convert(item, sb);
          conn2 = ",";
        }
        sb.append(")");
      } else if (attributes.get(key) != null && attributes.get(key)) {
        convert(strKey, sb);
        sb.append("{}(");
        if (isListOfVarsAttribute(key)) {
          convertStringVarList(location, freeVarsMap, strVal, sb);
        } else {
          switch (strKey) {
            case "unit", "element", "update" -> {
              Production prod = production(KApply(KLabel(strVal)));
              convert(prod.klabel().get(), prod.params(), sb);
              sb.append("()");
            }
            default -> sb.append(StringUtil.enquoteKString(strVal));
          }
        }
        sb.append(")");
      } else {
        convert(strKey, sb);
        sb.append("{}()");
      }
      conn = ", ";
    }
    sb.append("]");
  }

  private void convertStringVarList(
      HasLocation location, Map<String, KVariable> freeVarsMap, String strVal, StringBuilder sb) {
    if (strVal.trim().isEmpty()) return;
    Collection<KVariable> variables =
        Arrays.stream(strVal.split(","))
            .map(String::trim)
            .map(
                s -> {
                  if (freeVarsMap.containsKey(s)) return freeVarsMap.get(s);
                  else
                    throw KEMException.criticalError("No free variable found for " + s, location);
                })
            .toList();
    String conn = "";
    for (KVariable var : variables) {
      sb.append(conn);
      convert((K) var, sb);
      conn = ",";
    }
  }

  private boolean isListOfVarsAttribute(Att.Key name) {
    return name.equals(Att.CONCRETE()) || name.equals(Att.SYMBOLIC());
  }

  private static String[] asciiReadableEncodingKoreCalc() {
    String[] koreEncoder =
        Arrays.copyOf(
            StringUtil.asciiReadableEncodingDefault,
            StringUtil.asciiReadableEncodingDefault.length);
    koreEncoder[0x26] = "And-";
    koreEncoder[0x3c] = "-LT-";
    koreEncoder[0x3e] = "-GT-";
    koreEncoder[0x40] = "-AT-";
    koreEncoder[0x5e] = "Xor-";
    return koreEncoder;
  }

  private static final Pattern identChar = Pattern.compile("[A-Za-z0-9\\-]");
  public static String[] asciiReadableEncodingKore = asciiReadableEncodingKoreCalc();

  private static void convert(String name, StringBuilder sb) {
    switch (name) {
      case "module",
          "endmodule",
          "sort",
          "hooked-sort",
          "symbol",
          "hooked-symbol",
          "alias",
          "axiom" -> {
        sb.append(name).append("'Kywd'");
        return;
      }
      default -> {}
    }
    StringBuilder buffer = new StringBuilder();
    StringUtil.encodeStringToAlphanumeric(buffer, name, asciiReadableEncodingKore, identChar, "'");
    sb.append(buffer);
  }

  public Set<K> collectAnonymousVariables(K k) {
    Set<K> anonymousVariables = new HashSet<>();
    new VisitK() {
      @Override
      public void apply(KApply k) {
        if (mlBinders.contains(k.klabel().name())
            && k.items().get(0).att().contains(Att.ANONYMOUS())) {
          throw KEMException.internalError("Nested quantifier over anonymous variables.");
        }
        for (K item : k.items()) {
          apply(item);
        }
      }

      @Override
      public void apply(KVariable k) {
        if (k.att().contains(Att.ANONYMOUS())) {
          anonymousVariables.add(k);
        }
      }
    }.apply(k);
    return anonymousVariables;
  }

  public void convert(K k, StringBuilder sb) {
    new VisitK() {
      @Override
      public void apply(KApply k) {
        KLabel label = computePolyKLabel(k);
        String conn = "";
        if (mlBinders.contains(k.klabel().name())
            && k.items().get(0).att().contains(Att.ANONYMOUS())) {
          // Handle #Forall _ / #Exists _
          Set<K> anonymousVariables = collectAnonymousVariables(k.items().get(1));

          // Quantify over all anonymous variables.
          for (K variable : anonymousVariables) {
            sb.append(conn);
            convert(label, sb);
            sb.append("(");
            apply(variable);
            conn = ",";
          }

          // We assume that mlBinder only has two children.
          sb.append(conn);
          apply(k.items().get(1));

          for (int i = 0; i < anonymousVariables.size(); i++) {
            sb.append(")");
          }
        } else {
          convert(label, sb);
          sb.append("(");
          for (K item : k.items()) {
            sb.append(conn);
            apply(item);
            conn = ",";
          }
          sb.append(")");
        }
      }

      @Override
      public void apply(KToken k) {
        sb.append("\\dv{");
        convert(k.sort(), sb);
        sb.append("}(");
        if (module
            .sortAttributesFor()
            .get(k.sort().head())
            .getOrElse(Att::empty)
            .getOptional(Att.HOOK())
            .orElse("")
            .equals("STRING.String")) {
          sb.append(StringUtil.escapeNonASCII(k.s()));
        } else if (module
            .sortAttributesFor()
            .get(k.sort().head())
            .getOrElse(Att::empty)
            .getOptional(Att.HOOK())
            .orElse("")
            .equals("BYTES.Bytes")) {
          sb.append(StringUtil.escapeNonASCII(k.s().substring(1))); // remove the leading `b`
        } else {
          sb.append(StringUtil.enquoteKString(k.s()));
        }
        sb.append(")");
      }

      @Override
      public void apply(KSequence k) {
        for (int i = 0; i < k.items().size(); i++) {
          K item = k.items().get(i);
          boolean isList = item.att().get(Att.SORT(), Sort.class).equals(Sorts.K());
          if (i == k.items().size() - 1) {
            if (isList) {
              apply(item);
            } else {
              sb.append("kseq{}(");
              apply(item);
              sb.append(",dotk{}())");
            }
          } else {
            if (item.att().get(Att.SORT(), Sort.class).equals(Sorts.K())) {
              sb.append("append{}(");
            } else {
              sb.append("kseq{}(");
            }
            apply(item);
            sb.append(",");
          }
        }
        if (k.items().size() == 0) {
          sb.append("dotk{}()");
        }
        for (int i = 0; i < k.items().size() - 1; i++) {
          sb.append(")");
        }
      }

      @Override
      public void apply(KVariable k) {
        boolean setVar = k.name().startsWith("@");
        if (setVar) {
          sb.append('@');
        }
        sb.append("Var");
        String name = setVar ? k.name().substring(1) : k.name();
        convert(name, sb);
        sb.append(":");
        convert(k.att().getOptional(Att.SORT(), Sort.class).orElse(Sorts.K()), sb);
      }

      @Override
      public void apply(KRewrite k) {
        sb.append("\\rewrites{");
        convert(k.att().get(Att.SORT(), Sort.class), sb);
        sb.append("}(");
        apply(k.left());
        sb.append(",");
        apply(k.right());
        sb.append(")");
      }

      @Override
      public void apply(KAs k) {
        Sort sort = k.att().get(Att.SORT(), Sort.class);
        sb.append("\\and{");
        convert(sort, sb);
        sb.append("}(");
        apply(k.pattern());
        sb.append(",");
        apply(k.alias());
        sb.append(")");
      }

      @Override
      public void apply(InjectedKLabel k) {
        throw KEMException.internalError("Cannot yet translate #klabel to kore", k);
      }
    }.apply(k);
  }
}

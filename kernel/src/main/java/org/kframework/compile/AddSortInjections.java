// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.FoldK;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;

public class AddSortInjections {

  private final Module mod;
  private final Map<KLabel, KLabel> collectionFor;
  private final ConfigurationInfoFromModule configurationInfo;

  private int freshSortParamCounter = 0;
  private final Set<String> sortParams = new HashSet<>();
  public static final String SORTPARAM_NAME = "#SortParam";
  private boolean isLHS = false;

  public AddSortInjections(Module mod) {
    this.mod = mod;
    this.collectionFor = ConvertDataStructureToLookup.collectionFor(mod);
    this.configurationInfo = new ConfigurationInfoFromModule(mod);
  }

  public Sentence addInjections(Sentence s) {
    if (s instanceof RuleOrClaim) {
      return addInjections((RuleOrClaim) s);
    } else {
      return s;
    }
  }

  public RuleOrClaim addInjections(RuleOrClaim roc) {
    initSortParams();
    K body = addTopSortInjections(roc.body());
    K requires = internalAddSortInjections(roc.requires(), Sorts.Bool());
    K ensures = internalAddSortInjections(roc.ensures(), Sorts.Bool());
    Att att = roc.att();
    if (!sortParams.isEmpty()) {
      att =
          att.add(
              Att.SORT_PARAMS(),
              Sort.class,
              Sort("", sortParams.stream().map(s -> Sort(s)).collect(Collections.toList())));
    }
    return roc.newInstance(body, requires, ensures, att);
  }

  public K addInjections(K term) {
    Sort topSort = sort(term, Sorts.K());
    K result = addSortInjections(term, topSort);
    return result;
  }

  public K addSortInjections(K term, Sort topSort) {
    initSortParams();
    return internalAddSortInjections(term, topSort);
  }

  private boolean collectionIsMap(KLabel collectionLabel) {
    return mod.attributesFor().apply(collectionLabel).contains(Att.COMM())
        && !mod.attributesFor().apply(collectionLabel).contains(Att.IDEM())
        && !mod.attributesFor().apply(collectionLabel).contains(Att.BAG());
  }

  private K addTopSortInjections(K body) {
    if (new FoldK<Boolean>() {
      @Override
      public Boolean unit() {
        return false;
      }

      @Override
      public Boolean apply(KRewrite k) {
        return true;
      }

      @Override
      public Boolean merge(Boolean a, Boolean b) {
        return a || b;
      }
    }.apply(body)) {
      body = KRewrite(RewriteToTop.toLeft(body), RewriteToTop.toRight(body));
    }
    Sort sort = topSort(body);
    return internalAddSortInjections(body, sort);
  }

  private K internalAddSortInjections(K term, Sort expectedSort) {
    Sort actualSort = sort(term, expectedSort);
    if (actualSort == null) {
      actualSort = expectedSort;
    }
    if (actualSort.equals(expectedSort)) {
      return visitChildren(term, actualSort, expectedSort);
    } else if (expectedSort.equals(Sorts.K())) {
      if (actualSort.equals(Sorts.KItem())) {
        return KSequence(visitChildren(term, actualSort, expectedSort));
      } else {
        return KSequence(
            KApply(
                KLabel("inj", actualSort, Sorts.KItem()),
                KList(visitChildren(term, actualSort, expectedSort)),
                Att.empty().add(Att.SORT(), Sort.class, Sorts.KItem())));
      }
    } else {
      String hookAtt =
          mod.sortAttributesFor()
              .get(expectedSort.head())
              .getOrElse(() -> Att.empty())
              .getOptional(Att.HOOK())
              .orElse("");
      if ((hookAtt.equals("MAP.Map") || hookAtt.equals("SET.Set") || hookAtt.equals("LIST.List"))
          && term instanceof KApply) {
        for (KLabel collectionLabel : collectionFor.keySet()) {
          Optional<String> wrapElement =
              mod.attributesFor().apply(collectionLabel).getOptional(Att.WRAP_ELEMENT());
          if (wrapElement.isPresent()) {
            KLabel wrappedLabel = KLabel(wrapElement.get());
            KLabel elementLabel =
                KLabel(mod.attributesFor().apply(collectionLabel).get(Att.ELEMENT()));
            KApply k = (KApply) term;
            if (configurationInfo.getCellSort(wrappedLabel).equals(actualSort)) {
              if (collectionIsMap(collectionLabel)) {
                // Map
                K key;
                if (k.klabel().equals(wrappedLabel)) {
                  key = k.klist().items().get(0);
                } else {
                  key =
                      KApply(
                          KLabel(expectedSort.name() + "Key"),
                          KList(visitChildren(k, actualSort, expectedSort)));
                }
                Sort adjustedExpectedSort = expectedSort;
                if (k.att().contains(Att.SORT(), Sort.class)) {
                  adjustedExpectedSort = k.att().get(Att.SORT(), Sort.class);
                }
                Production prod = production(k);
                Production substituted =
                    substituteProd(
                        prod,
                        adjustedExpectedSort,
                        (i, fresh) -> sort(k.items().get(i), fresh.nonterminals().apply(i).sort()),
                        k);
                Sort expectedKeySort = substituted.nonterminal(0).sort();
                Sort actualKeySort = sort(key, expectedKeySort);
                return KApply(
                    elementLabel,
                    KList(
                        visitChildren(key, actualKeySort, expectedKeySort),
                        visitChildren(k, actualSort, expectedSort)),
                    Att.empty().add(Att.SORT(), Sort.class, expectedSort));
              } else {
                return KApply(
                    elementLabel,
                    KList(visitChildren(k, actualSort, expectedSort)),
                    Att.empty().add(Att.SORT(), Sort.class, expectedSort));
              }
            }
          }
        }
      }
      return KApply(
          KLabel("inj", actualSort, expectedSort),
          KList(visitChildren(term, actualSort, expectedSort)),
          Att.empty().add(Att.SORT(), Sort.class, expectedSort));
    }
  }

  private void initSortParams() {
    freshSortParamCounter = 0;
    sortParams.clear();
  }

  private K visitChildren(K term, Sort actualSort, Sort expectedSort) {
    Att att = term.att().add(Att.SORT(), Sort.class, actualSort);
    if (actualSort.name().equals(SORTPARAM_NAME)) {
      sortParams.add(actualSort.params().head().name());
    }
    if (term instanceof KApply kapp) {
      if (kapp.klabel().name().equals("inj")) {
        return term;
      }
      if (kapp.att().contains(Att.SORT(), Sort.class)) {
        expectedSort = kapp.att().get(Att.SORT(), Sort.class);
      }
      Production prod = production(kapp);
      List<K> children = new ArrayList<>();
      Production substituted =
          substituteProd(
              prod,
              expectedSort,
              (i, fresh) -> sort(kapp.items().get(i), fresh.nonterminals().apply(i).sort()),
              kapp);
      for (int i = 0; i < kapp.items().size(); i++) {
        if (kapp.items().size() != substituted.nonterminals().size()) {
          throw KEMException.compilerError(
              "Invalid sort predicate "
                  + kapp.klabel()
                  + " that depends directly or indirectly on the current configuration. "
                  + "Is it possible to replace the sort predicate with a regular function?",
              kapp);
        }
        Sort expectedSortOfChild = substituted.nonterminal(i).sort();
        K child = kapp.items().get(i);
        children.add(internalAddSortInjections(child, expectedSortOfChild));
      }
      return KApply(substituted.klabel().get(), KList(children), att);
    } else if (term instanceof KRewrite rew) {
      isLHS = true;
      K lhs = internalAddSortInjections(rew.left(), actualSort);
      isLHS = false;
      return KRewrite(lhs, internalAddSortInjections(rew.right(), actualSort), att);
    } else if (term instanceof KVariable) {
      return KVariable(((KVariable) term).name(), att);
    } else if (term instanceof KToken) {
      return KToken(((KToken) term).s(), ((KToken) term).sort(), att);
    } else if (term instanceof InjectedKLabel) {
      return InjectedKLabel(((InjectedKLabel) term).klabel(), att);
    } else if (term instanceof KSequence kseq) {
      List<K> children = new ArrayList<>();
      for (int i = 0; i < kseq.size(); i++) {
        K child = kseq.items().get(i);
        Sort childSort = sort(child, isLHS ? Sorts.KItem() : Sorts.K());
        if (childSort.equals(Sorts.K())) {
          children.add(internalAddSortInjections(child, Sorts.K()));
        } else {
          children.add(internalAddSortInjections(child, Sorts.KItem()));
        }
      }
      return KSequence(children, att);
    } else if (term instanceof KAs kas) {
      return KAs(internalAddSortInjections(kas.pattern(), actualSort), kas.alias(), att);
    } else {
      throw KEMException.internalError("Invalid category of k found.", term);
    }
  }

  /**
   * Generate the substituted production with its sort parameters added for a parametric production.
   *
   * @param prod The production to add sort parameters to.
   * @param expectedSort the sort context where the term with the specified production appears.
   * @param getSort a function taking the 0-based index of the child of this production and the
   *     substitutedFresh production and returning the sort of the child.
   * @param loc The location to report upon an error.
   * @return The production substituted with the least upper bounds of its sort parameters based on
   *     its children's sorts.
   */
  public Production substituteProd(
      Production prod,
      Sort expectedSort,
      BiFunction<Integer, Production, Sort> getSort,
      HasLocation loc) {
    Production substituted = prod;
    List<Sort> args = new ArrayList<>();
    List<Sort> fresh = new ArrayList<>();
    for (int i = 0; i < prod.params().size(); i++) {
      if (prod.params().apply(i).equals(prod.sort())) {
        fresh.add(expectedSort);
      } else {
        fresh.add(freshSortParam());
      }
    }
    Production substitutedFresh = prod.substitute(immutable(fresh));
    if (prod.params().nonEmpty()) {
      Map<Sort, List<Sort>> subst = new HashMap<>();
      for (int i = 0; i < prod.nonterminals().size(); i++) {
        Sort declaredSort = prod.nonterminals().apply(i).sort();
        Sort actual = getSort.apply(i, substitutedFresh);
        match(prod, declaredSort, actual, subst);
      }
      int i = 0;
      matchExpected(prod, expectedSort, subst);
      for (Sort param : iterable(prod.params())) {
        if (subst.get(param) == null) {
          args.add(fresh.get(i));
        } else {
          args.add(lub(subst.get(param), fresh.get(i), loc, mod));
        }
        i++;
      }
      substituted = prod.substitute(immutable(args));
    }
    return substituted;
  }

  private void match(
      Production prod, Sort declaredSort, Sort actualSort, Map<Sort, List<Sort>> subst) {
    if (prod.isSortVariable(declaredSort)) {
      subst.computeIfAbsent(declaredSort, s -> new ArrayList<>()).add(actualSort);
      return;
    }
    if (actualSort.params().size() == declaredSort.params().size()
        && actualSort.head().equals(declaredSort.head())) {
      for (int i = 0; i < declaredSort.head().params(); i++) {
        match(prod, declaredSort.params().apply(i), actualSort.params().apply(i), subst);
      }
    }
    for (Sort s : iterable(mod.allSorts())) {
      if (mod.subsorts().lessThanEq(s, actualSort)) {
        if (s.params().size() == declaredSort.params().size()
            && s.head().equals(declaredSort.head())) {
          for (int i = 0; i < declaredSort.head().params(); i++) {
            match(prod, declaredSort.params().apply(i), s.params().apply(i), subst);
          }
        }
      }
    }
  }

  /**
   * Compute the sort of a term in a context where there is no expected sort, i.e., at the top of a
   * rule body.
   */
  public Sort topSort(K term) {
    return sort(term, freshSortParam());
  }

  /** Compute the sort of a term with a particular expected sort. */
  public Sort sort(K term, Sort expectedSort) {
    if (term instanceof KApply kapp) {
      if (kapp.klabel().name().equals("inj")) {
        return kapp.klabel().params().apply(1);
      }
      if (kapp.klabel().name().startsWith("#SemanticCastTo")) {
        return Outer.parseSort(kapp.klabel().name().substring("#SemanticCastTo".length()));
      }
      if (kapp.klabel().name().equals("#fun2")) {
        return sort(kapp.items().get(0), expectedSort);
      }
      if (kapp.klabel().name().equals("#fun3")) {
        return sort(kapp.items().get(1), expectedSort);
      }
      if (kapp.klabel().name().equals("#let")) {
        return sort(kapp.items().get(2), expectedSort);
      }
      if (kapp.klabel().name().equals("_:=K_")) {
        return Sorts.Bool();
      }
      if (kapp.klabel().name().equals("_:/=K_")) {
        return Sorts.Bool();
      }
      if (kapp.att().contains(Att.SORT(), Sort.class)) {
        expectedSort = kapp.att().get(Att.SORT(), Sort.class);
      }
      Production prod = production(kapp);
      Production substituted = prod;
      List<Sort> args = new ArrayList<>();
      List<Sort> fresh = new ArrayList<>();
      for (int i = 0; i < prod.params().size(); i++) {
        if (prod.params().apply(i).equals(prod.sort())) {
          fresh.add(expectedSort);
        } else {
          fresh.add(freshSortParam());
        }
      }
      Production substitutedFresh = prod.substitute(immutable(fresh));
      if (prod.params().nonEmpty()) {
        Map<Sort, List<Sort>> subst = new HashMap<>();
        for (int i = 0; i < prod.nonterminals().size(); i++) {
          Sort declaredSort = prod.nonterminals().apply(i).sort();
          Sort actual = sort(kapp.items().get(i), substitutedFresh.nonterminals().apply(i).sort());
          match(prod, declaredSort, actual, subst);
        }
        int i = 0;
        matchExpected(prod, expectedSort, subst);
        for (Sort param : iterable(prod.params())) {
          if (subst.get(param) == null) {
            args.add(fresh.get(i));
          } else {
            args.add(lub(subst.get(param), fresh.get(i), kapp, mod));
          }
          i++;
        }
        substituted = prod.substitute(immutable(args));
      }
      return substituted.sort();
    } else if (term instanceof KRewrite rew) {
      Sort leftSort = sort(rew.left(), expectedSort);
      Sort rightSort = sort(rew.right(), expectedSort);
      return lubSort(leftSort, rightSort, expectedSort, term, mod);
    } else if (term instanceof KToken) {
      return ((KToken) term).sort();
    } else if (term instanceof KVariable) {
      return term.att().getOptional(Att.SORT(), Sort.class).orElse(Sorts.K());
    } else if (term instanceof KSequence) {
      return Sorts.K();
    } else if (term instanceof InjectedKLabel) {
      return Sorts.KItem();
    } else if (term instanceof KAs as) {
      Sort patternSort = sort(as.pattern(), expectedSort);
      Sort rightSort = sort(as.alias(), expectedSort);
      return lubSort(patternSort, rightSort, expectedSort, term, mod);
    } else {
      throw KEMException.internalError("Invalid category of k found.", term);
    }
  }

  private void matchExpected(Production prod, Sort expectedSort, Map<Sort, List<Sort>> subst) {
    boolean found = false;
    outer:
    for (Sort param : iterable(prod.params())) {
      if (!prod.sort().contains(param)) {
        continue;
      }
      for (NonTerminal nt : iterable(prod.nonterminals())) {
        if (nt.sort().contains(param)) {
          continue outer;
        }
      }
      found = true;
    }
    if (found) {
      match(prod, prod.sort(), expectedSort, subst);
    }
  }

  public static Sort lubSort(
      Sort leftSort, Sort rightSort, Sort expectedSort, HasLocation loc, Module mod) {
    if (leftSort == null && rightSort == null) {
      return expectedSort;
    } else if (leftSort == null) {
      return rightSort;
    } else if (rightSort == null) {
      return leftSort;
    }
    return lub(Arrays.asList(leftSort, rightSort), expectedSort, loc, mod);
  }

  private Production production(KApply term) {
    Option<scala.collection.immutable.Set<Production>> prods =
        mod.productionsFor().get(term.klabel().head());
    if (prods.isEmpty()) {
      throw KEMException.compilerError(
          "Could not find productions for KApply with label "
              + term.klabel()
              + " in module "
              + mod.name(),
          term);
    }
    return prods.get().head();
  }

  private static Sort lub(
      Collection<Sort> entries, Sort expectedSort, HasLocation loc, Module mod) {
    assert !entries.isEmpty();
    entries = new HashSet<>(entries);
    Collection<Sort> filteredEntries =
        entries.stream().filter(s -> s != null && !s.name().equals(SORTPARAM_NAME)).toList();
    if (filteredEntries.isEmpty()) { // if all sorts are parameters, take the first
      return entries.iterator().next();
    }

    Set<Sort> nonParametric =
        filteredEntries.stream().filter(s -> s.params().isEmpty()).collect(Collectors.toSet());
    Set<Sort> bounds = mod.subsorts().upperBounds(nonParametric);
    // Anything less than KBott or greater than K is a syntactic sort from kast.md which should not
    // be considered
    bounds.removeIf(
        s ->
            mod.subsorts().lessThanEq(s, Sorts.KBott())
                || mod.subsorts().greaterThan(s, Sorts.K()));
    if (expectedSort != null && !expectedSort.name().equals(SORTPARAM_NAME)) {
      bounds.removeIf(s -> !mod.subsorts().lessThanEq(s, expectedSort));
    }

    // For parametric sorts, each bound must bound at least one instantiation
    Set<Sort> parametric =
        filteredEntries.stream().filter(s -> !s.params().isEmpty()).collect(Collectors.toSet());
    bounds.removeIf(
        bound ->
            parametric.stream()
                .anyMatch(
                    param ->
                        stream(mod.definedInstantiations().apply(param.head()))
                            .noneMatch(inst -> mod.subsorts().lessThanEq(inst, bound))));

    Set<Sort> lub = mod.subsorts().minimal(bounds);
    if (lub.size() != 1) {
      throw KEMException.internalError(
          "Could not compute least upper bound for rewrite sort. Possible candidates: " + lub, loc);
    }
    return lub.iterator().next();
  }

  private Sort freshSortParam() {
    return Sort(SORTPARAM_NAME, Sort("Q" + freshSortParamCounter++));
  }
}

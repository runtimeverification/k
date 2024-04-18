// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.parser.inner.RuleGrammarGenerator;

public class GenerateSortProjections {

  private Module mod;
  private final Module mainMod;
  private final boolean cover;

  public GenerateSortProjections(boolean cover, Module mainMod) {
    this.mainMod = mainMod;
    this.cover = cover;
  }

  public GenerateSortProjections(Module mod) {
    this.mainMod = null;
    this.mod = mod;
    this.cover = false;
  }

  public Module gen(Module mod) {
    this.mod = mod;
    return Module(
        mod.name(),
        mod.imports(),
        mod.localSentences()
            .$bar(
                immutable(
                    Stream.concat(
                            stream(mod.allSorts()).flatMap(this::gen),
                            stream(mod.localProductions()).flatMap(this::gen))
                        .collect(Collectors.toSet())))
            .toSet(),
        mod.att());
  }

  public static KLabel getProjectLbl(Sort sort) {
    KLabel lbl;
    lbl = KLabel("project:" + sort.toString());
    return lbl;
  }

  public static KLabel getProjectLbl(String klabel, String name) {
    return KLabel("project:" + klabel + ":" + name);
  }

  public Stream<? extends Sentence> gen(Sort sort) {
    if (RuleGrammarGenerator.isParserSort(sort)
        && !sort.equals(Sorts.KItem())
        && !sort.equals(Sorts.K())) {
      return Stream.empty();
    }
    KLabel lbl = getProjectLbl(sort);
    KVariable var = KVariable("K", Att.empty().add(Att.SORT(), Sort.class, sort));
    Rule r =
        Rule(
            KRewrite(KApply(lbl, var), var),
            BooleanUtils.TRUE,
            BooleanUtils.TRUE,
            Att.empty().add(Att.PROJECTION()));
    if (mod.definedKLabels().contains(lbl)) {
      return Stream.empty();
    }
    Production prod =
        Production(
            lbl,
            sort,
            Seq(Terminal(lbl.name()), Terminal("("), NonTerminal(Sorts.K()), Terminal(")")),
            Att.empty().add(Att.FUNCTION()).add(Att.PROJECTION()));
    if (cover) {
      KLabel sideEffectLbl = KLabel("sideEffect:" + sort);
      Production sideEffect =
          Production(
              sideEffectLbl,
              sort,
              Seq(
                  Terminal(sideEffectLbl.name()),
                  Terminal("("),
                  NonTerminal(Sorts.K()),
                  Terminal(","),
                  NonTerminal(sort),
                  Terminal(")")),
              Att.empty().add(Att.FUNCTION()));
      Rule sideEffectR =
          Rule(
              KRewrite(
                  KApply(
                      sideEffectLbl,
                      KVariable("K2", Att.empty().add(Att.SORT(), Sort.class, Sorts.K())),
                      var),
                  var),
              BooleanUtils.TRUE,
              BooleanUtils.TRUE);
      return stream(Collections.<Sentence>Set(prod, r, sideEffect, sideEffectR));
    } else {
      return stream(Collections.<Sentence>Set(prod, r));
    }
  }

  public Stream<? extends Sentence> gen(Production prod) {
    if (prod.att().contains(Att.FUNCTION())
        || (prod.klabel().isDefined() && mod.macroKLabels().contains(prod.klabel().get()))) {
      return Stream.empty();
    }
    java.util.Set<Sentence> sentences = new HashSet<>();
    List<K> vars = new ArrayList<>();
    int i = 0;
    boolean hasName = false;
    for (NonTerminal nt : iterable(prod.nonterminals())) {
      vars.add(KVariable("K" + i++, Att.empty().add(Att.SORT(), Sort.class, nt.sort())));
      hasName = hasName || nt.name().isDefined();
    }
    if (!hasName) {
      return Stream.empty();
    }
    boolean total = false;
    if (mainMod != null) {
      if (stream(
                  mainMod
                      .productionsForSort()
                      .get(prod.sort().head())
                      .getOrElse(() -> Collections.<Production>Set()))
              .filter(p -> !p.att().contains(Att.FUNCTION()))
              .count()
          == 1) {
        total = true;
      }
    }
    i = 0;
    for (NonTerminal nt : iterable(prod.nonterminals())) {
      if (nt.name().isDefined()) {
        KLabel lbl = getProjectLbl(prod.klabel().get().name(), nt.name().get());
        if (mod.definedKLabels().contains(lbl)) {
          return Stream.empty();
        }
        Att att = Att.empty().add(Att.FUNCTION());
        if (total) {
          att = att.add(Att.TOTAL());
        }
        sentences.add(
            Production(
                lbl,
                nt.sort(),
                Seq(
                    Terminal(nt.name().get()),
                    Terminal("("),
                    NonTerminal(prod.sort()),
                    Terminal(")")),
                att));
        sentences.add(
            Rule(
                KRewrite(KApply(lbl, KApply(prod.klabel().get(), KList(vars))), vars.get(i)),
                BooleanUtils.TRUE,
                BooleanUtils.TRUE));
      }
      i++;
    }
    return sentences.stream();
  }
}

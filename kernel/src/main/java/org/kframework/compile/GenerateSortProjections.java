// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.Collections;
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
import org.kframework.parser.inner.generator.RuleGrammarGenerator;
import scala.collection.Set;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class GenerateSortProjections {

    private Module mod;
    private final boolean cover;

    public GenerateSortProjections(boolean cover) {
        this.cover = cover;
    }

    public GenerateSortProjections(Module mod) {
      this.mod = mod;
      this.cover = false;
    }

    public Module gen(Module mod) {
        this.mod = mod;
        return Module(mod.name(), mod.publicImports(), mod.privateImports(), (Set<Sentence>) mod.localSentences().$bar(
              Stream.concat(stream(mod.allSorts()).flatMap(this::gen),
                stream(mod.localProductions()).flatMap(this::gen)).collect(Collections.toSet())), mod.att());
    }

    public static KLabel getProjectLbl(Sort sort, Module m) {
        KLabel lbl;
        lbl = KLabel("project:" + sort.toString());
        return lbl;
    }

    public static KLabel getProjectLbl(String klabel, String name) {
      return KLabel("project:" + klabel + ":" + name);
    }

    public Stream<? extends Sentence> gen(Sort sort) {
        if (RuleGrammarGenerator.isParserSort(sort) && !sort.equals(Sorts.KItem()) && !sort.equals(Sorts.K())) {
            return Stream.empty();
        }
        KLabel lbl = getProjectLbl(sort, mod);
        KVariable var = KVariable("K", Att.empty().add(Sort.class, sort));
        Rule r = Rule(KRewrite(KApply(lbl, var), var), BooleanUtils.TRUE, BooleanUtils.TRUE, Att().add("projection"));
        if (mod.definedKLabels().contains(lbl)) {
            return Stream.empty();
        }
        Production prod = Production(lbl, sort, Seq(Terminal(lbl.name()), Terminal("("), NonTerminal(Sorts.K()), Terminal(")")), Att().add("function").add("projection"));
        if (cover) {
            KLabel sideEffectLbl = KLabel("sideEffect:" + sort.toString());
            Production sideEffect = Production(sideEffectLbl, sort, Seq(Terminal(sideEffectLbl.name()), Terminal("("), NonTerminal(Sorts.K()), Terminal(","), NonTerminal(sort), Terminal(")")), Att().add("function"));
            Rule sideEffectR = Rule(KRewrite(KApply(sideEffectLbl, KVariable("K2", Att.empty().add(Sort.class, Sorts.K())), var), var), BooleanUtils.TRUE, BooleanUtils.TRUE);
            return stream(Set(prod, r, sideEffect, sideEffectR));
        } else {
            return stream(Set(prod, r));
        }
    }

    public Stream<? extends Sentence> gen(Production prod) {
      if (prod.att().contains(Att.FUNCTION())) {
        return Stream.empty();
      }
      java.util.Set<Sentence> sentences = new HashSet<>();
      List<K> vars = new ArrayList<>();
      int i = 0;
      boolean hasName = false;
      for (NonTerminal nt : iterable(prod.nonterminals())) {
        vars.add(KVariable("K" + i++, Att.empty().add(Sort.class, nt.sort())));
        hasName = hasName || nt.name().isDefined();
      }
      if (!hasName) {
        return Stream.empty();
      }
      i = 0;
      for (NonTerminal nt : iterable(prod.nonterminals())) {
        if (nt.name().isDefined()) {
          KLabel lbl = getProjectLbl(prod.klabel().get().name(), nt.name().get());
          if (mod.definedKLabels().contains(lbl)) {
              return Stream.empty();
          }
          sentences.add(Production(lbl, nt.sort(), Seq(Terminal(nt.name().get()), Terminal("("), NonTerminal(prod.sort()), Terminal(")")), Att().add("function")));
          sentences.add(Rule(KRewrite(KApply(lbl, KApply(prod.klabel().get(), KList(vars))), vars.get(i)), BooleanUtils.TRUE, BooleanUtils.TRUE));
        }
        i++;
      }
      return sentences.stream();
    }


}

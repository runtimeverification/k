// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Hooks;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;

public class ResolveStrict {

  private final Definition d;

  private Module currentModule;

  public ResolveStrict(Definition d) {
    this.d = d;
  }

  public Set<Sentence> resolve(Set<Production> strictProductions) {
    Set<Sentence> sentences = new HashSet<>();
    for (Production prod : strictProductions) {
      if (!prod.klabel().isDefined()) {
        throw KEMException.compilerError("Only productions with a KLabel can be strict.", prod);
      }
      if (prod.att().contains(Att.STRICT())) {
        sentences.addAll(resolve(prod, false));
      }
      if (prod.att().contains(Att.SEQSTRICT())) {
        sentences.addAll(resolve(prod, true));
      }
    }
    return sentences;
  }

  private static KApply cast(Sort sort, K k) {
    return KApply(KLabel("#SemanticCastTo" + sort.toString()), k);
  }

  public static void setPositions(
      String attribute, List<Integer> strictnessPositions, long arity, Production loc) {
    String[] strictAttrs = attribute.split(",");
    for (String strictAttr : strictAttrs) {
      try {
        int pos = Integer.parseInt(strictAttr.trim());
        if (pos < 1 || pos > arity) throw new IndexOutOfBoundsException();
        strictnessPositions.add(pos);
      } catch (NumberFormatException | IndexOutOfBoundsException e) {
        if (arity == 0) {
          throw KEMException.compilerError(
              "Cannot put a strict attribute on a production with no nonterminals", loc);
        } else {
          throw KEMException.compilerError(
              "Expecting a number between 1 and "
                  + arity
                  + ", but found "
                  + strictAttr
                  + " as a"
                  + " strict position in "
                  + Arrays.toString(strictAttrs),
              loc);
        }
      }
    }
  }

  private void setAliases(String attribute, Set<ContextAlias> aliases, Production prod) {
    String[] strictAttrs = attribute.split(",");
    for (String strictAttr : strictAttrs) {
      String label = strictAttr.trim();
      Option<scala.collection.immutable.Set<Sentence>> ss = d.mainModule().labeled().get(label);
      if (ss.isDefined()) {
        for (Sentence s : iterable(ss.get())) {
          if (s instanceof ContextAlias) {
            aliases.add((ContextAlias) s);
          } else {
            throw KEMException.compilerError(
                "Found rule label \""
                    + label
                    + "\" in strictness attribute of production "
                    + prod
                    + " which does not refer to a context alias.",
                s);
          }
        }
      } else {
        throw KEMException.compilerError(
            "Found rule label \""
                + label
                + "\" in strictness attribute which did not refer to any sentence.",
            prod);
      }
    }
  }

  private static final ContextAlias DEFAULT_ALIAS =
      ContextAlias(KVariable("HERE"), BooleanUtils.TRUE, Att.empty());

  private void resolve(
      boolean sequential,
      Set<Sentence> sentences,
      long arity,
      List<Integer> strictnessPositions,
      List<Integer> allPositions,
      Set<ContextAlias> aliases,
      Production production) {
    for (int i = 0; i < strictnessPositions.size(); i++) {
      List<K> items = new ArrayList<>();
      for (int j = 0; j < arity; j++) {
        // Preserve sort information of the production
        items.add(cast(production.nonterminal(j).sort(), KVariable("K" + j)));
      }
      int strictnessPosition = strictnessPositions.get(i) - 1;
      K hole;
      // Preserve sort information of the production
      hole = cast(production.nonterminal(strictnessPosition).sort(), KVariable("HOLE"));

      for (ContextAlias alias : aliases) {
        K body =
            new TransformK() {
              @Override
              public K apply(KVariable var) {
                if (var.name().equals("HERE")) {
                  K thisHole = hole;
                  if (alias.att().contains(Att.CONTEXT())) {
                    KLabel contextLabel = KLabel(alias.att().get(Att.CONTEXT()));
                    thisHole = KRewrite(hole, KApply(contextLabel, hole));
                  }
                  items.set(strictnessPosition, thisHole);
                  return KApply(production.klabel().get(), KList(items));
                }
                return var;
              }
            }.apply(alias.body());

        Sort result = Outer.parseSort(alias.att().getOptional(Att.RESULT()).orElse("KResult"));

        // is seqstrict the elements before the argument should be KResult
        Optional<KApply> sideCondition =
            Stream.concat(allPositions.stream(), strictnessPositions.subList(0, i).stream())
                .map(j -> KApply(KLabel("is" + result.toString()), KVariable("K" + (j - 1))))
                .reduce(BooleanUtils::and);
        K requires;
        if (sideCondition.isEmpty() || !sequential) {
          requires = BooleanUtils.TRUE;
        } else {
          requires = sideCondition.get();
        }

        String label =
            currentModule.name()
                + "."
                + production.klabelAtt().get().replace("`", "").replaceAll("\\s", "")
                + (strictnessPosition + 1);

        Context ctx =
            Context(
                body,
                BooleanUtils.and(requires, alias.requires()),
                production.att().addAll(alias.att()).add(Att.LABEL(), label));
        sentences.add(ctx);
      }
    }
  }

  public Set<Sentence> resolve(Production production, boolean sequential) {
    long arity = production.nonterminals().size();
    List<Integer> strictnessPositions = new ArrayList<>();
    List<Integer> allPositions = new ArrayList<>();
    Set<ContextAlias> aliases = new HashSet<>();
    String attribute;
    Set<Sentence> sentences = new HashSet<>();
    if (sequential) {
      attribute = production.att().get(Att.SEQSTRICT());
    } else {
      attribute = production.att().get(Att.STRICT());
    }
    if (attribute.isEmpty()) {
      for (int i = 1; i <= arity; i++) {
        strictnessPositions.add(i);
      }
      aliases.add(DEFAULT_ALIAS);
      resolve(sequential, sentences, arity, strictnessPositions, allPositions, aliases, production);
      allPositions.addAll(strictnessPositions);
    } else {
      String[] components = attribute.split(";");
      if (components.length == 1) {
        if (Character.isDigit(components[0].trim().charAt(0))) {
          aliases.add(DEFAULT_ALIAS);
          setPositions(components[0].trim(), strictnessPositions, arity, production);
        } else {
          for (int i = 1; i <= arity; i++) {
            strictnessPositions.add(i);
          }
          setAliases(components[0].trim(), aliases, production);
        }
        resolve(
            sequential, sentences, arity, strictnessPositions, allPositions, aliases, production);
        allPositions.addAll(strictnessPositions);
      } else if (components.length % 2 == 0) {
        for (int i = 0; i < components.length; i += 2) {
          setAliases(components[i].trim(), aliases, production);
          setPositions(components[i + 1].trim(), strictnessPositions, arity, production);
          resolve(
              sequential, sentences, arity, strictnessPositions, allPositions, aliases, production);
          aliases.clear();
          allPositions.addAll(strictnessPositions);
          strictnessPositions.clear();
        }
      } else {
        throw KEMException.compilerError(
            "Invalid strict attribute containing multiple semicolons.", production);
      }
    }

    if (production.att().contains(Att.HYBRID())) {
      List<KLabel> results = new ArrayList<>();
      if (!production.att().get(Att.HYBRID()).equals("")) {
        String[] sorts = StringUtil.splitOneDimensionalAtt(production.att().get(Att.HYBRID()));
        for (String sort : sorts) {
          results.add(KLabel("is" + sort));
        }
      } else {
        results.add(KLabel("isKResult"));
      }
      for (KLabel result : results) {
        List<K> items = new ArrayList<>();
        for (int j = 0; j < arity; j++) {
          // Preserve sort information of the production
          items.add(cast(production.nonterminal(j).sort(), KVariable("K" + j)));
        }
        K term = KApply(production.klabel().get(), KList(items));
        Optional<KApply> sideCondition =
            allPositions.stream()
                .map(j -> KApply(result, KVariable("K" + (j - 1))))
                .reduce(BooleanUtils::and);
        K requires;
        if (sideCondition.isEmpty()) {
          requires = BooleanUtils.TRUE;
        } else {
          requires = sideCondition.get();
        }
        Rule hybrid =
            Rule(KRewrite(KApply(result, term), BooleanUtils.TRUE), requires, BooleanUtils.TRUE);
        sentences.add(hybrid);
      }
    }
    return sentences;
  }

  public Module resolve(Module input) {
    currentModule = input;
    Set<Sentence> contextsToAdd =
        resolve(
            stream(input.localSentences())
                .filter(s -> s instanceof Production)
                .map(s -> (Production) s)
                .filter(p -> p.att().contains(Att.STRICT()) || p.att().contains(Att.SEQSTRICT()))
                .collect(Collectors.toSet()));
    scala.collection.immutable.Set<Import> imports = input.imports();
    // strictness makes use _andBool_ found in the BOOL module. Make sure it's imported
    if (!contextsToAdd.isEmpty() && !input.importedModuleNames().contains(Hooks.BOOL))
      imports = Set(Import.apply(d.getModule(Hooks.BOOL).get(), false)).$bar(imports).toSet();
    return Module(
        input.name(),
        imports,
        stream(input.localSentences())
            .filter(s -> !(s instanceof ContextAlias))
            .collect(Collections.toSet())
            .$bar(immutable(contextsToAdd))
            .toSet(),
        input.att());
  }
}

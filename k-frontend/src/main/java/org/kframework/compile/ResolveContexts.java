// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kore.FindK;
import org.kframework.kore.FoldK;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

public class ResolveContexts {

  public ResolveContexts() {}

  public Definition resolve(Definition d) {
    klabels = new HashSet<>();
    Module transformedMainModule = resolve(d.mainModule());
    return Definition.apply(
        transformedMainModule,
        add(transformedMainModule, minus(d.mainModule(), d.entryModules())),
        d.att());
  }

  public Module resolve(Module input) {
    Set<Sentence> rulesToAdd =
        stream(input.sentences())
            .filter(s -> s instanceof Context)
            .map(s -> (Context) s)
            .flatMap(c -> this.resolve(c, input))
            .collect(Collectors.toCollection(HashSet::new));
    if (!rulesToAdd.isEmpty()) {
      rulesToAdd.add(SyntaxSort(Seq(), Sorts.K()));
    }
    return Module(
        input.name(),
        input.imports(),
        stream(input.localSentences())
            .filter(s -> !(s instanceof Context))
            .collect(Collections.toSet())
            .$bar(immutable(rulesToAdd))
            .toSet(),
        input.att());
  }

  private Set<KLabel> klabels;

  private KLabel getUniqueFreezerLabel(Module input, String nameHint) {
    if (klabels.isEmpty()) {
      klabels.addAll(mutable(input.definedKLabels()));
    }
    int counter = 0;
    KLabel freezer;
    do {
      freezer = KLabel("#freezer" + nameHint + "_" + (counter++ == 0 ? "" : counter));
    } while (klabels.contains(freezer));
    klabels.add(freezer);
    return freezer;
  }

  private Att addSuffixToLabel(Att a, String suffix) {
    if (!a.contains(Att.LABEL())) {
      return a;
    }
    return a.add(Att.LABEL(), a.get(Att.LABEL()) + suffix);
  }

  private Stream<? extends Sentence> resolve(Context context, Module input) {
    checkContextValidity(context);
    final SortedMap<KVariable, K> vars = new TreeMap<>((v1, v2) -> v1.name().compareTo(v2.name()));
    K body = context.body();
    K requiresHeat = context.requires();
    K requiresCool = BooleanUtils.TRUE;

    int[] currentHolePosition = new int[] {0};
    int[] finalHolePosition = new int[] {0};
    // does this context have a main cell?
    boolean hasMainCell =
        new FoldK<Boolean>() {
          @Override
          public Boolean apply(KApply k) {
            if (input
                .attributesFor()
                .getOrElse(k.klabel(), () -> Att.empty())
                .contains(Att.MAINCELL())) {
              return true;
            }
            return super.apply(k);
          }

          @Override
          public Boolean unit() {
            return false;
          }

          @Override
          public Boolean merge(Boolean a, Boolean b) {
            return a || b;
          }
        }.apply(body);

    // Find a heated hole
    // e.g., context ++(HOLE => lvalue(HOLE))
    K heated =
        new VisitK() {
          K heated;
          KVariable holeVar;
          boolean inMainCell = false;

          public K process(K k) {
            apply(k);
            if (heated != null) return heated;
            else return holeVar;
          }

          @Override
          public void apply(KRewrite k) {
            heated = k.right();
            super.apply(k);
          }

          @Override
          public void apply(KVariable k) {
            if (inMainCell || !hasMainCell) {
              if (!k.name().equals("HOLE")) {
                vars.put(k, k);
                currentHolePosition[0]++;
              } else {
                holeVar = k;
                finalHolePosition[0] = currentHolePosition[0];
              }
            }
            super.apply(k);
          }

          @Override
          public void apply(KApply k) {
            if (input
                .attributesFor()
                .getOrElse(k.klabel(), () -> Att.empty())
                .contains(Att.MAINCELL())) {
              inMainCell = true;
            }
            if (k.klabel() instanceof KVariable && (inMainCell || !hasMainCell))
              vars.put((KVariable) k.klabel(), InjectedKLabel(k.klabel()));
            super.apply(k);
            if (input
                .attributesFor()
                .getOrElse(k.klabel(), () -> Att.empty())
                .contains(Att.MAINCELL())) {
              inMainCell = false;
            }
          }
        }.process(body);
    K cooled =
        new VisitK() {
          K cooled;

          public K process(K k) {
            apply(k);
            if (cooled != null) return cooled;
            else return k;
          }

          @Override
          public void apply(KApply k) {
            if (input
                .attributesFor()
                .getOrElse(k.klabel(), () -> Att.empty())
                .contains(Att.MAINCELL())) {
              cooled = k.items().get(1);
            }
            super.apply(k);
          }
        }.process(RewriteToTop.toLeft(body));

    // TODO(dwightguth): generate freezers better for pretty-printing purposes
    List<ProductionItem> items = new ArrayList<>();
    KLabel freezerLabel;
    if (cooled instanceof KApply kApply) {
      String name = kApply.klabel().name();
      if (name.equals("#SemanticCastToK")) {
        K firstArg = kApply.klist().items().get(0);
        if (firstArg instanceof KApply) name = ((KApply) firstArg).klabel().name();
      }
      freezerLabel = getUniqueFreezerLabel(input, name + finalHolePosition[0]);
    } else {
      freezerLabel = getUniqueFreezerLabel(input, "");
    }
    items.add(Terminal(freezerLabel.name()));
    items.add(Terminal("("));
    for (int i = 0; i < vars.size(); i++) {
      items.add(NonTerminal(Sorts.K()));
      items.add(Terminal(","));
    }
    if (vars.size() > 0) {
      items.remove(items.size() - 1);
    }
    items.add(Terminal(")"));
    Production freezer = Production(freezerLabel, Sorts.KItem(), immutable(items), Att.empty());
    K frozen = KApply(freezerLabel, vars.values().stream().collect(Collections.toList()));

    Att heatAtt = addSuffixToLabel(context.att().add(Att.HEAT()), "-heat");
    Att coolAtt = addSuffixToLabel(context.att().add(Att.COOL()), "-cool");

    Function<String, Void> throwException =
        label -> {
          Sentence loc = input.labeled().get(label).get().head();
          throw KEMException.compilerError(
              "The generated label for a context rule conflicts with a user-defined label at "
                  + loc.source().get()
                  + " and "
                  + loc.location().get()
                  + ". Please consider renaming.",
              context);
        };

    if (heatAtt.contains(Att.LABEL())) {
      String label = heatAtt.get(Att.LABEL());
      if (input.labeled().contains(label)) {
        throwException.apply(label);
      }
    }

    if (coolAtt.contains(Att.LABEL())) {
      String label = coolAtt.get(Att.LABEL());
      if (input.labeled().contains(label)) {
        throwException.apply(label);
      }
    }

    return Stream.of(
        freezer,
        Rule(
            insert(body, KRewrite(cooled, KSequence(heated, frozen)), input),
            requiresHeat,
            BooleanUtils.TRUE,
            heatAtt),
        Rule(
            insert(body, KRewrite(KSequence(heated, frozen), cooled), input),
            requiresCool,
            BooleanUtils.TRUE,
            coolAtt));
  }

  private K insert(K body, K rewrite, Module mod) {
    class Holder {
      boolean found = false;
    }
    Holder h = new Holder();
    K inserted =
        new TransformK() {
          @Override
          public K apply(KApply k) {
            if (mod.attributesFor()
                .getOrElse(k.klabel(), () -> Att.empty())
                .contains(Att.MAINCELL())) {
              h.found = true;
              return KApply(k.klabel(), k.items().get(0), rewrite, k.items().get(2));
            }
            return super.apply(k);
          }
        }.apply(body);
    if (h.found) {
      return inserted;
    } else {
      return rewrite;
    }
  }

  /**
   * Check validity of context.
   *
   * <p>Currently the following conditions are checked: - Contexts must have at least one HOLE. -
   * Contexts must have a single rewrite. - Only the HOLE can be rewritten in a context definition.
   *
   * @param context to be checked
   */
  public static void checkContextValidity(Context context) {
    K body = context.body();

    int cntHoles =
        new FindK() {
          @Override
          public scala.collection.Set<K> apply(KVariable k) {
            if (k.name().equals("HOLE")) {
              return org.kframework.Collections.<K>Set(k);
            } else {
              return super.apply(k);
            }
          }
        }.apply(body).size();
    if (cntHoles < 1) {
      throw KEMException.compilerError("Contexts must have at least one HOLE.", context);
    }

    int cntRewrites =
        new FindK() {
          @Override
          public scala.collection.Set<K> apply(KRewrite k) {
            return this.merge(org.kframework.Collections.<K>Set(k), super.apply(k));
          }
        }.apply(body).size();
    if (cntRewrites > 1) {
      throw KEMException.compilerError("Cannot compile a context with multiple rewrites.", context);
    }

    new VisitK() {
      @Override
      public void apply(KRewrite k) {
        if (!isHOLE(k.left())) {
          throw KEMException.compilerError(
              "Only the HOLE can be rewritten in a context definition", context);
        }
        super.apply(k);
      }

      // return true when k is either HOLE or #SemanticCastToX(HOLE)
      private boolean isHOLE(K k) {
        if (k instanceof KApply kapp) {
          return kapp.klabel().name().startsWith("#SemanticCastTo")
              && kapp.klist().size() == 1
              && isHOLEVar(kapp.klist().items().get(0));
        } else {
          return isHOLEVar(k);
        }
      }

      private boolean isHOLEVar(K k) {
        return k instanceof KVariable && ((KVariable) k).name().equals("HOLE");
      }
    }.apply(body);
  }
}
